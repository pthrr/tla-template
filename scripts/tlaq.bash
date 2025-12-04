#!/usr/bin/env bash
set -euo pipefail

echo_error() {
  printf "\033[1;31m%s\033[0m\n" "$*"
}

# Parse command
CMD="${1:-help}"
shift || true

# Parse remaining args
BACKEND="tlc"
SPEC=""
EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
  case $1 in
    --backend|-b)
      BACKEND="$2"
      shift 2
      ;;
    *)
      if [[ -z "$SPEC" ]]; then
        SPEC="$1"
        shift
      else
        # Save remaining args for subcommands
        EXTRA_ARGS+=("$1")
        shift
      fi
      ;;
  esac
done

# Validate backend
if [[ "$BACKEND" != "tlc" && "$BACKEND" != "apalache" ]]; then
  echo_error "❌ Invalid backend '$BACKEND'. Must be 'tlc' or 'apalache'."
  exit 1
fi

# Strip .tla extension if present
if [[ -n "$SPEC" && "$SPEC" == *.tla ]]; then
  SPEC="${SPEC%.tla}"
fi

# Set paths (will be set even if SPEC is empty, commands can check)
TLA="${SPEC}.tla"
CFG="${SPEC}.cfg"
JAR="${TLA2TOOLS_JAR:-tla2tools.jar}"
JSON_JAR="${TLA2JSON_JAR:-tla2json.jar}"
APALACHE_JAR="${APALACHE_JAR:-apalache.jar}"
JAVA_OPTS="${JAVA_OPTS:-"-Xmx2G -XX:+UseParallelGC"}"

echo_error() {
  printf "\033[1;31m%s\033[0m\n" "$*"
}

echo_warn() {
  printf "\033[1;33m %s\033[0m\n" "$*"
}

echo_info() {
  printf "\033[1;36m %s\033[0m\n" "$*"
}

echo_success() {
  printf "\033[1;32m%s\033[0m\n" "$*"
}

require_tool() {
  command -v "$1" >/dev/null || { echo_error "❌ Required tool '$1' not found."; exit 1; }
}

require_toolchain() {
  case "$1" in
    tlc)
      require_tool java
      [[ -f "$JAR" ]] || { echo_error "❌ TLC jar not found: $JAR"; exit 1; }
      ;;
    apalache)
      require_tool java
      [[ -f "$APALACHE_JAR" ]] || { echo_error "❌ Apalache jar not found: $APALACHE_JAR"; exit 1; }
      ;;
  esac
}

describe_toolchain() {
  echo "🔧 Toolchain check for backend: $BACKEND"
  echo ""
  echo "Required:"
  case "$BACKEND" in
    tlc)
      echo -n "• java: "; command -v java >/dev/null && java -version 2>&1 | head -n1 || echo_error "❌ missing"
      echo -n "• jar:  "; [[ -f "$JAR" ]] && echo "$JAR" || echo_error "❌ missing"
      ;;
    apalache)
      echo -n "• java: "; command -v java >/dev/null && java -version 2>&1 | head -n1 || echo_error "❌ missing"
      echo -n "• jar:  "; [[ -f "$APALACHE_JAR" ]] && echo "$APALACHE_JAR" || echo_error "❌ missing"
      ;;
  esac
  echo -n "• python3: "; command -v python3 >/dev/null && python3 --version || echo_error "❌ missing"

  echo ""
  echo "Optional:"
  echo -n "• jq (for JSON formatting): "; command -v jq >/dev/null && jq --version || echo_warn "⚠️  not installed"
  echo -n "• dot/graphviz (for PNG plots): "; command -v dot >/dev/null && dot -V 2>&1 || echo_warn "⚠️  not installed"
  echo -n "• pandoc (for docs): "; command -v pandoc >/dev/null && pandoc --version | head -n1 || echo_warn "⚠️  not installed"
  echo -n "• inotifywait (for watch): "; command -v inotifywait >/dev/null && inotifywait --version 2>&1 | head -n1 || echo_warn "⚠️  not installed"
  echo -n "• tla2json.jar: "; [[ -f "$JSON_JAR" ]] && echo "$JSON_JAR" || echo_warn "⚠️  not found"
}

check_files() {
  [[ -f "$TLA" ]] || { echo_error "❌ Spec file '$TLA' not found."; exit 1; }

  if [[ "$BACKEND" = "tlc" && ! -f "$CFG" ]]; then
    echo "⚠️  Config file '$CFG' not found. Generating a default..."
    echo "INIT Init" > "$CFG"
    echo "NEXT Next" >> "$CFG"
    grep -q "TypeInvariant *==" "$TLA" && echo "INVARIANT TypeInvariant" >> "$CFG"
    echo "✅ Auto-generated $CFG"
  fi
}

run_backend_check() {
  require_toolchain "$BACKEND"
  check_files

  # Detect number of CPU cores
  local nworkers=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

  case "$BACKEND" in
    apalache)
      echo "🔍 [Apalache] Checking..."
      # Use TLC config file if it exists
      local config_args=()
      if [[ -f "$CFG" ]]; then
        config_args=("--config=$CFG")
      fi
      # Limit search depth
      java $JAVA_OPTS -jar "$APALACHE_JAR" check --length=5 "${config_args[@]}" "$TLA"
      ;;
    tlc)
      echo "🔍 [TLC] Model checking (${nworkers} workers)..."

      if grep -q -- '--algorithm' "$TLA"; then
        java $JAVA_OPTS -cp "$JAR" pcal.trans "$TLA"
      fi

      # Dump trace to JSON on error
      java $JAVA_OPTS -cp "$JAR" tlc2.TLC -workers $nworkers -deadlock -tool -config $CFG \
        -dumpTrace json "${SPEC}_trace.json" "$TLA"
      ;;
  esac
}

run_backend_simulate() {
  require_toolchain "$BACKEND"
  if [[ "$BACKEND" = "apalache" ]]; then
    echo "❌ Apalache does not support simulation."
  else
    echo "🎲 [TLC] Simulating 10 random traces..."
    java $JAVA_OPTS -cp "$JAR" tlc2.TLC -simulate -depth 10 -config "$CFG" "$TLA"
  fi
}

run_apalache_types() {
  echo "🧠 [Apalache] Showing inferred types..."
  java $JAVA_OPTS -jar "$APALACHE_JAR" typecheck "$TLA"
}

dump_trace_tlc() {
  [[ -f "${SPEC}.out" ]] || { echo "❌ No TLC trace file."; exit 1; }
  echo "📜 [TLC] Trace:"
  awk '/Trace:/ {found=1; next} found && NF {print}' "${SPEC}.out"
}

dump_trace_json() {
  require_tool java

  if [[ ! -f "$JSON_JAR" ]]; then
    echo_error "❌ Missing JSON JAR: $JSON_JAR"
    exit 1
  fi

  echo_info "📤 Converting TLC trace to JSON using $JSON_JAR..."
  java -jar "$JSON_JAR" --spec "$TLA" --output "${SPEC}.trace.json"
  jq '.' "${SPEC}.trace.json"
}

clean_artifacts() {
  echo "🧹 Cleaning up..."
  rm -rf *.out *.trace *.json *.dot "${SPEC}_MC" "${SPEC}.cfg.trace"
}

init_spec() {
  local name=""
  local vars=""
  local init_expr=""
  local next_expr=""
  local invariant=""
  local property=""

  while [[ $# -gt 0 ]]; do
    case $1 in
      --name)       name="$2"; shift 2;;
      --vars)       vars="$2"; shift 2;;
      --init)       init_expr="$2"; shift 2;;
      --next)       next_expr="$2"; shift 2;;
      --invariant)  invariant="$2"; shift 2;;
      --property)   property="$2"; shift 2;;
      *) echo "❌ Unknown option: $1"; return 1;;
    esac
  done

  [[ -z "$name" ]] && echo "❌ --name is required." && return 1

  [[ "$name" =~ ^[a-zA-Z_][a-zA-Z0-9_]*$ ]] || {
    echo_error "❌ Invalid spec name: $name"
    exit 1
  }

  local tla="${name}.tla"
  local cfg="${name}.cfg"

  [[ -z "$vars" ]] && vars="x"
  [[ -z "$init_expr" ]] && init_expr="x = 0"
  [[ -z "$next_expr" ]] && next_expr="x < 5 /\\ x' = x + 1"
  [[ -z "$invariant" ]] && invariant="x \\in 0..5"
  [[ -z "$property" ]] && property="x <= 5"

  if [[ -f "$tla" ]]; then
    echo "❌ File '$tla' already exists."
    return 1
  fi

  cat > "$tla" <<EOF
----------------------------- MODULE ${name} -----------------------------

EXTENDS Naturals

VARIABLES ${vars}

Init == ${init_expr}

Next == ${next_expr}

TypeInvariant == ${invariant}

Safety == ${property}

=============================================================================
EOF

  cat > "$cfg" <<EOF
INIT Init
NEXT Next
INVARIANT TypeInvariant
PROPERTY Safety
EOF

  echo "✅ Created spec: $tla"
  echo "✅ Created config: $cfg"
  echo "💡 You can now run: tlaq check tlc $name"
}

list_specs() {
  echo "📄 Found .tla specs:"
  find . -maxdepth 1 -name "*.tla" | sort
}

watch_spec() {
  require_tool inotifywait
  local name="$1"
  echo "👀 Watching $name.tla for changes..."
  while inotifywait -e close_write "$name.tla" 2>/dev/null; do
    echo "🔁 Detected change. Re-checking..."
    ./tlaq check "$BACKEND" "$name"
  done
}

plot_trace() {
  local script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  local plot_script="$script_dir/plot-trace.py"
  local trace_file="${SPEC}_trace.json"

  if [[ ! -f "$plot_script" ]]; then
    echo_error "❌ plot-trace.py not found: $plot_script"
    exit 1
  fi

  if [[ ! -f "$trace_file" ]]; then
    echo_error "❌ No trace file: $trace_file"
    exit 1
  fi

  python3 "$plot_script" "$trace_file" "${EXTRA_ARGS[@]}"
}

case "$CMD" in
  check|run)
    run_backend_check
    ;;
  simulate)
    run_backend_simulate
    ;;
  trace|pretty)
    dump_trace_tlc
    ;;
  json)
    dump_trace_json
    ;;
  plot)
    plot_trace
    ;;
  types)
    [[ "$BACKEND" = "apalache" ]] && run_apalache_types || echo "❌ TLC does not support types."
    ;;
  clean)
    clean_artifacts
    ;;
  init)
    shift
    init_spec "$@"
    ;;
  list)
    list_specs
    ;;
  doctor)
    describe_toolchain
    ;;
  watch)
    [[ -z "${3:-}" ]] && echo "❌ Usage: tlaq watch <backend> <SpecName>" && exit 1
    watch_spec "$SPEC"
    ;;
  help|--help|-h)
    cat <<EOF
Usage: tlaq <command> <subcommand> <SpecName>

Available commands:
  check       Run model checker (TLC or Apalache)
  simulate    Simulate random traces (TLC only)
  trace       Show counterexample trace (TLC)
  json        Export TLC trace to JSON
  plot        Visualize trace (--dot FILE | --mermaid FILE | --table)
  types       Show inferred types (Apalache)
  init        Create new .tla and .cfg files with scaffolding
  list        List .tla spec files
  watch       Re-check on save (requires inotify-tools)
  clean       Delete build outputs

Examples:
  tlaq check tlc MySpec
  tlaq check apalache MySpec
  tlaq plot MySpec
  tlaq plot MySpec --dot trace.dot
  tlaq init --name MySpec --vars x --init 'x = 0' --next \"x' = x + 1\"
EOF
    ;;
  *)
    echo "❌ Unknown command '$CMD'"
    exit 1
    ;;
esac

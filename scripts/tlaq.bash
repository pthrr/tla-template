#!/usr/bin/env bash
set -euo pipefail

CMD="${1:-help}"
BACKEND="${2:-tlc}"
SPEC="${3:-MySpec}"

if ! [[ "$SPEC" =~ ^[a-zA-Z_][a-zA-Z0-9_]*$ ]]; then
  echo_error "❌ Invalid spec name. Use letters, digits, or underscores only."
  exit 1
fi

TLA="${SPEC}.tla"
CFG="${SPEC}.cfg"
JAR="${TLA2TOOLS_JAR:-tla2tools.jar}"
JSON_JAR="${TLA2JSON_JAR:-tla2json.jar}"
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
      require_tool apalache
      ;;
  esac
}

describe_toolchain() {
  echo "🔧 Toolchain check for backend: $BACKEND"
  case "$BACKEND" in
    tlc)
      echo -n "• java: "; command -v java >/dev/null && java -version 2>&1 | head -n1 || echo_error "❌ missing"
      echo -n "• jar:  "; [[ -f "$JAR" ]] && echo "$JAR" || echo_error "❌ missing"
      ;;
    apalache)
      echo -n "• apalache: "; command -v apalache || echo_error "❌ missing"
      ;;
  esac
  echo -n "• jq: "; command -v jq >/dev/null && jq --version || echo_error "❌ missing"
  echo -n "• pandoc: "; command -v pandoc >/dev/null && pandoc --version | head -n1 || echo_error "❌ missing"
  echo -n "• inotifywait: "; command -v inotifywait || echo_error "❌ missing"
  echo -n "• tla2json.jar: "; [[ -f "$JSON_JAR" ]] && echo "$JSON_JAR" || echo_error "❌ missing"
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
  case "$BACKEND" in
    apalache)
      echo "🔍 [Apalache] Checking..."
      apalache check "$TLA"
      ;;
    tlc)
      echo "🔍 [TLC] Model checking..."

      if grep -q -- '--algorithm' "$TLA"; then
        java $JAVA_OPTS -cp "$JAR" pcal.trans "$TLA"
      fi

      java $JAVA_OPTS -cp "$JAR" tlc2.TLC -deadlock -tool -config $CFG "$TLA"
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
  apalache typecheck "$TLA"
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
  types       Show inferred types (Apalache)
  init        Create new .tla and .cfg files with scaffolding
  list        List .tla spec files
  watch       Re-check on save (requires inotify-tools)
  clean       Delete build outputs

Examples:
  tlaq check tlc MySpec
  tlaq check apalache MySpec
  tlaq init --name MySpec --vars x --init 'x = 0' --next \"x' = x + 1\"
EOF
    ;;
  *)
    echo "❌ Unknown command '$CMD'"
    exit 1
    ;;
esac

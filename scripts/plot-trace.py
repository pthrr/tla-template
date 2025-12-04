#!/usr/bin/env python3
"""
Visualize TLA+ traces from JSON output.
Usage: tlaq json SpecName | plot-trace.py
"""
import json
import sys
from pathlib import Path

def print_trace_table(trace_data):
    """Print trace as formatted table."""
    states = trace_data if isinstance(trace_data, list) else [trace_data]

    print("\n" + "="*80)
    print("TRACE VISUALIZATION")
    print("="*80)

    for i, state in enumerate(states):
        action = state.get('action', state.get('_action', 'State'))
        print(f"\n[State {i}] {action}")
        print("-" * 80)

        for key, val in sorted(state.items()):
            if not key.startswith('_') and key != 'action':
                val_str = json.dumps(val) if isinstance(val, (dict, list)) else str(val)
                print(f"  {key:20s} = {val_str}")

def generate_dot(trace_data, output_path, render_png=False):
    """Generate GraphViz DOT file."""
    import shutil

    states = trace_data if isinstance(trace_data, list) else [trace_data]

    lines = [
        "digraph Trace {",
        "  rankdir=TB;",
        "  node [shape=box, style=rounded, fontname=monospace];",
        ""
    ]

    for i, state in enumerate(states):
        action = state.get('action', f'State{i}')
        # Build label
        label_parts = [f"<b>State {i}</b>", action, ""]
        for key, val in sorted(state.items()):
            if not key.startswith('_') and key != 'action':
                val_str = str(val)[:40]
                label_parts.append(f"{key} = {val_str}")

        label = "\\n".join(label_parts).replace('"', '\\"')
        lines.append(f'  s{i} [label="{label}"];')

        if i > 0:
            lines.append(f'  s{i-1} -> s{i};')

    lines.append("}")

    output_path.write_text('\n'.join(lines))
    print(f"✅ Generated: {output_path}", file=sys.stderr)

    if render_png:
        if not shutil.which('dot'):
            print(f"❌ Error: graphviz (dot) is required to render PNG", file=sys.stderr)
            print(f"💡 Install with: sudo dnf install graphviz", file=sys.stderr)
            sys.exit(1)

        png_path = output_path.with_suffix('.png')
        import subprocess
        subprocess.run(['dot', '-Tpng', str(output_path), '-o', str(png_path)], check=True)
        print(f"✅ Generated: {png_path}", file=sys.stderr)
    elif shutil.which('dot'):
        print(f"💡 Render with: dot -Tpng {output_path} -o {output_path.with_suffix('.png')}", file=sys.stderr)
    else:
        print(f"⚠️  Install graphviz to render PNG: sudo dnf install graphviz", file=sys.stderr)

def generate_mermaid(trace_data, output_path):
    """Generate Mermaid diagram."""
    states = trace_data if isinstance(trace_data, list) else [trace_data]

    lines = ["graph TD"]

    for i, state in enumerate(states):
        action = state.get('action', f'State{i}')
        label = f"State {i}: {action}"
        lines.append(f'  s{i}["{label}"]')

        if i > 0:
            lines.append(f'  s{i-1} --> s{i}')

    output_path.write_text('\n'.join(lines))
    print(f"✅ Generated: {output_path}", file=sys.stderr)
    print(f"💡 View at: https://mermaid.live/", file=sys.stderr)

def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="Visualize TLA+ traces",
        epilog="Examples:\n  tlaq json ChordDHT | plot-trace.py\n  plot-trace.py trace.json --dot trace.dot",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('input', nargs='?', default='-', help='JSON file or "-" for stdin')
    parser.add_argument('--dot', type=Path, help='Output GraphViz DOT file')
    parser.add_argument('--png', type=Path, help='Output PNG file (requires graphviz)')
    parser.add_argument('--mermaid', type=Path, help='Output Mermaid diagram')
    parser.add_argument('--table', action='store_true', help='Print table (default if no output specified)')

    args = parser.parse_args()

    # Read JSON
    if args.input == '-':
        data = json.load(sys.stdin)
    else:
        with open(args.input) as f:
            data = json.load(f)

    # Default to table if no output specified
    if not args.dot and not args.png and not args.mermaid and not args.table:
        args.table = True

    # Generate outputs
    if args.table:
        print_trace_table(data)

    if args.png:
        # PNG requires dot, generate both DOT and PNG
        dot_path = args.png.with_suffix('.dot')
        generate_dot(data, dot_path, render_png=True)
    elif args.dot:
        generate_dot(data, args.dot, render_png=False)

    if args.mermaid:
        generate_mermaid(data, args.mermaid)

    return 0

if __name__ == '__main__':
    sys.exit(main())

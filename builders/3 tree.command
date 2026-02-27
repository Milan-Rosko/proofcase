#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Rocq/Coq project dependency "tree" generator
# Layout: Vertical (Top-to-Bottom) for better website integration.
# -----------------------------------------------------------------------------

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"

# Output directory
OUT_DIR="${OUT_DIR:-$ROOT/scratch}"
mkdir -p "$OUT_DIR"

# Check for shadow build first
DEFAULT_SHADOW_THEORIES="$ROOT/scratch/shadow/theories"
DEFAULT_SHADOW_CP="$ROOT/scratch/shadow/_CoqProject"

if [[ -d "$DEFAULT_SHADOW_THEORIES" && -f "$DEFAULT_SHADOW_CP" ]]; then
  THEORY_DIR="${THEORY_DIR:-$DEFAULT_SHADOW_THEORIES}"
  COQPROJECT="${COQPROJECT:-$DEFAULT_SHADOW_CP}"
  ORIGIN="shadow"
else
  THEORY_DIR="${THEORY_DIR:-$ROOT/theories}"
  COQPROJECT="${COQPROJECT:-$ROOT/_CoqProject}"
  ORIGIN="repo"
fi

DEPS_RAW="$OUT_DIR/deps.raw"
DOT="$OUT_DIR/deps.dot"
EDGES="$OUT_DIR/deps.edges"
TSORT_OUT="$OUT_DIR/deps.tsort"

if ! command -v coqdep >/dev/null 2>&1; then
  echo "ERROR: coqdep not found in PATH."
  echo "Make sure Rocq/Coq is installed and coqdep is available."
  exit 1
fi

if [[ ! -f "$COQPROJECT" ]]; then
  echo "ERROR: _CoqProject not found at: $COQPROJECT"
  exit 1
fi

if [[ ! -d "$THEORY_DIR" ]]; then
  echo "ERROR: theories directory not found at: $THEORY_DIR"
  exit 1
fi

echo "Using sources:   $ORIGIN"
echo "THEORY_DIR:      $THEORY_DIR"
echo "COQPROJECT:      $COQPROJECT"
echo "OUT_DIR:         $OUT_DIR"

# MacOS compatible file reading
VFILES=()
while IFS= read -r line; do
  VFILES+=("$line")
done < <(find "$THEORY_DIR" -type f -name '*.v' | sort)

if [[ "${#VFILES[@]}" -eq 0 ]]; then
  echo "ERROR: no .v files found under: $THEORY_DIR"
  exit 1
fi

echo "Running coqdep..."
coqdep -f "$COQPROJECT" "${VFILES[@]}" > "$DEPS_RAW"

# -----------------------------------------------------------------------------
# GENERATE DOT FILE AND EDGE LIST
# -----------------------------------------------------------------------------

# Pre-calculate directory lengths for label shortening
DIR_LEN=${#THEORY_DIR}
DIR_LEN=$((DIR_LEN + 1)) # +1 for slash

# We use perl to join escaped lines first, then awk to build the graph.
perl -pe 's/\\\n/ /g' "$DEPS_RAW" | \
awk -v theory_dir="$THEORY_DIR" -v dir_len="$DIR_LEN" '
function normalize(path) {
    # Strip extension
    sub(/\.vo$/, ".v", path)
    sub(/\.glob$/, ".v", path)
    return path
}

function prettify(path) {
    # 1. Try to strip the known absolute root path
    if (index(path, theory_dir) == 1) {
        path = substr(path, dir_len + 1)
    } 
    # Fallback: if path is still absolute but didnt match theory_dir perfectly, 
    # try to grep just the part after "theories/"
    else if (match(path, /\/theories\/.*/)) {
        path = substr(path, RSTART + 10) # +10 to skip "/theories/"
    }

    # 2. Shorten the hierarchy (skip first folder like M001... if possible)
    n = split(path, parts, "/")
    if (n > 1) {
        short_path = ""
        for (i = 2; i <= n; i++) {
            sep = (i == 2 ? "" : "/")
            short_path = short_path sep parts[i]
        }
        return short_path
    }
    return path
}

BEGIN {
    print "digraph RocqDeps {" > "'"$DOT"'"
    # CHANGED: rankdir=TB (Top to Bottom) instead of LR (Left to Right)
    print "  rankdir=TB;" > "'"$DOT"'"
    print "  node [shape=box, fontsize=10, style=filled, fillcolor=\"white\"];" > "'"$DOT"'"
    print "  edge [fontsize=9];" > "'"$DOT"'"
    print "" > "'"$DOT"'"
}

{
    # Line format: target.vo target.glob: dep1.v dep2.v ...
    n = split($0, chunks, ":")
    if (n < 2) next
    
    left = chunks[1]
    # Re-join right side
    right = ""
    for (i = 2; i <= n; i++) right = right (i==2?"":":") chunks[i]

    # --- Process Source Node ---
    split(left, targets, " ")
    src = ""
    for (i in targets) {
        if (targets[i] ~ /\.vo$/) {
            src = normalize(targets[i])
            break
        }
    }
    if (src == "") src = normalize(targets[1])

    # Add Source Node
    if (!(src in seen_nodes)) {
        lbl = prettify(src)
        print "  \"" src "\" [label=\"" lbl "\"];" > "'"$DOT"'"
        seen_nodes[src] = 1
    }

    # --- Process Dependencies (Edges) ---
    split(right, deps, " ")
    for (i in deps) {
        d = deps[i]
        
        # 1. Normalize extension FIRST (converts .vo -> .v)
        d = normalize(d)

        # 2. Filter: Must be a .v file now
        if (d !~ /\.v$/) continue
        
        # 3. Filter: Ignore self-loops
        if (src == d) continue
        
        # 4. Filter: Must be inside our source tree
        if (index(d, "/") == 1 && index(d, theory_dir) != 1) continue

        # Draw Edge
        edge_key = src "->" d
        if (!(edge_key in seen_edges)) {
            print "  \"" src "\" -> \"" d "\";" > "'"$DOT"'"
            print src "\t" d > "'"$EDGES"'"
            seen_edges[edge_key] = 1
        }
        
        # Ensure Dep Node exists visually
        if (!(d in seen_nodes)) {
            lbl = prettify(d)
            print "  \"" d "\" [label=\"" lbl "\"];" > "'"$DOT"'"
            seen_nodes[d] = 1
        }
    }
}

END {
    print "}" > "'"$DOT"'"
}
'

# Topological sort
if [[ -s "$EDGES" ]]; then
  awk -F'\t' '{print $2, $1}' "$EDGES" | tsort > "$TSORT_OUT"
else
  echo "No edges found for tsort." > "$TSORT_OUT"
fi

# Render SVG
if command -v dot >/dev/null 2>&1; then
  dot -Tsvg "$DOT" -o "$OUT_DIR/deps.svg"
  echo "Wrote: $OUT_DIR/deps.svg"
else
  echo "Graphviz not found (dot). Skipping SVG render."
  echo "Install: brew install graphviz"
fi

echo "Wrote: $DEPS_RAW"
echo "Wrote: $DOT"
echo "Wrote: $EDGES"
echo "Wrote: $TSORT_OUT"
echo
echo "Open graph:"
echo "  open \"$OUT_DIR/deps.svg\""
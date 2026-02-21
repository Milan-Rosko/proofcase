#!/usr/bin/env bash
# builders/concat.command

set -Eeuo pipefail

die() { echo "Error: $*" >&2; exit 2; }

TTY="/dev/tty"
have_tty() { [[ -r "$TTY" && -w "$TTY" ]]; }
is_interactive_stdin() { [[ -t 0 ]]; }

pause() {
  if have_tty; then
    printf "\nPress Enter to close..." >"$TTY"
    IFS= read -r _ <"$TTY" || true
  elif is_interactive_stdin; then
    printf "\nPress Enter to close..." >&2
    IFS= read -r _ || true
  fi
}

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

trap 'rc=$?; ((rc!=0)) && echo >&2 && echo "Concat failed (exit status: $rc)." >&2; pause; exit $rc' EXIT

BUILD="$ROOT/scratch"
mkdir -p "$BUILD"

OUT="$ROOT/builders/v.context.txt"
LISTING="$BUILD/selected_files.txt"

ROOT_CP="$ROOT/_CoqProject"
THEORIES_CP="$ROOT/theories/_CoqProject"
# We define the directory to search for _Textslect files
TEXTSLECT_DIR="$ROOT/builders"

prompt_num() {
  local q="$1" def="$2" min="$3" max="$4" ans
  local in_fd out_fd

  if have_tty; then
    in_fd="$TTY"; out_fd="$TTY"
  else
    in_fd="/dev/stdin"; out_fd="/dev/stderr"
  fi

  if ! have_tty && ! is_interactive_stdin; then
    echo "$def"
    return 0
  fi

  while true; do
    printf "%s" "$q" >"$out_fd"
    IFS= read -r ans <"$in_fd" || true
    ans="${ans:-$def}"
    if [[ "$ans" =~ ^[0-9]+$ ]] && (( ans >= min && ans <= max )); then
      echo "$ans"
      return 0
    fi
    printf "Please enter a number in [%s-%s].\n" "$min" "$max" >"$out_fd"
  done
}

# --- NEW: Dynamic File Discovery ---

# Enable nullglob so the array is empty if no matches are found
shopt -s nullglob
# Find all files starting with _Textslect in the builders folder
TEXTSLECT_CANDIDATES=("$TEXTSLECT_DIR"/_Textslect*)
shopt -u nullglob

NUM_CANDIDATES=${#TEXTSLECT_CANDIDATES[@]}
COQ_OPTION=$((NUM_CANDIDATES + 1))

# Print Menu
if have_tty; then
  OUTPUT_FD="$TTY"
else
  OUTPUT_FD="/dev/stderr"
fi

printf "\nConcatenate from:\n" >"$OUTPUT_FD"

# List Textslect options
i=0
for cand in "${TEXTSLECT_CANDIDATES[@]}"; do
  i=$((i+1))
  # Show only the filename, not the full path
  name=$(basename "$cand")
  printf "  %d. %s\n" "$i" "$name" >"$OUTPUT_FD"
done

# List CoqProject option
printf "  %d. _CoqProject (local order)\n\n" "$COQ_OPTION" >"$OUTPUT_FD"

# Get Selection
SRC_CHOICE="$(prompt_num "Selection [1-$COQ_OPTION] (default 1): " "1" 1 "$COQ_OPTION")"

SRC_NAME=""
SRC_PATH=""

# --- Logic to handle Selection ---

if (( SRC_CHOICE <= NUM_CANDIDATES )); then
  # Array is 0-indexed, so subtract 1 from choice
  IDX=$((SRC_CHOICE - 1))
  SRC_PATH="${TEXTSLECT_CANDIDATES[$IDX]}"
  SRC_NAME="$(basename "$SRC_PATH")"
  
  [[ -f "$SRC_PATH" ]] || die "Expected $SRC_PATH. File went missing?"
else
  # This matches the old "else" block for CoqProject
  if [[ -f "$ROOT_CP" ]]; then
    SRC_NAME="_CoqProject (root)"
    SRC_PATH="$ROOT_CP"
  elif [[ -f "$THEORIES_CP" ]]; then
    SRC_NAME="_CoqProject (theories)"
    SRC_PATH="$THEORIES_CP"
  else
    die "No _CoqProject found at $ROOT_CP or $THEORIES_CP"
  fi
fi

echo "Output:"
echo "  OUT:     $OUT"
echo "  LISTING: $LISTING"
echo "Source:"
echo "  $SRC_NAME: $SRC_PATH"
echo

SELECTED_FILES=()

append_if_exists() {
  local rel="$1"
  [[ -z "$rel" ]] && return 0
  rel="${rel#./}"
  local src="$ROOT/$rel"
  [[ -f "$src" ]] || die "Listed file not found: $src"
  SELECTED_FILES+=("$rel")
}

# Read loop based on whether it is a _Textslect variant or CoqProject
if [[ "$SRC_NAME" == _Textslect* ]]; then
  # Parsing logic for _Textslect files
  while IFS= read -r line || [[ -n "$line" ]]; do
    line="${line%$'\r'}"
    [[ -z "$line" ]] && continue
    [[ "$line" =~ ^# ]] && continue
    line="$(printf "%s" "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
    [[ -z "$line" ]] && continue
    append_if_exists "$line"
  done <"$SRC_PATH"
else
  # Parsing logic for _CoqProject
  while IFS= read -r line || [[ -n "$line" ]]; do
    line="${line%$'\r'}"
    l="$(printf "%s" "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
    [[ -z "$l" ]] && continue
    [[ "$l" =~ ^# ]] && continue
    case "$l" in
      -Q*|-R*|-I*|-arg*|-coqlib*|-include*|-exclude*) continue ;;
    esac
    for tok in $l; do
      [[ "$tok" == "-q" ]] && continue
      case "$tok" in
        /*) die "Absolute project file entry not supported here (make it relative): $tok" ;;
        *.v) append_if_exists "$tok" ;;
      esac
    done
  done <"$SRC_PATH"
fi

COUNT="${#SELECTED_FILES[@]}"
if [[ "$COUNT" -eq 0 ]]; then
  echo "Warning: selected 0 files from $SRC_NAME." >&2
fi

: >"$LISTING"
for f in "${SELECTED_FILES[@]}"; do
  printf "%s\n" "$f" >>"$LISTING"
done

echo "Selected files: $COUNT"
echo

UTC_NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
: >"$OUT"

{
  echo "(* Note. This is a concatenation for establishing context. *)"
  echo "(* Source: $SRC_NAME *)"
  echo "(* Generated (UTC): $UTC_NOW *)"
  echo
  echo "(* ---- BEGIN $SRC_NAME ---- *)"
  while IFS= read -r src_line || [[ -n "$src_line" ]]; do
    src_line="${src_line%$'\r'}"
    printf "(* %s *)\n" "$src_line"
  done <"$SRC_PATH"
  echo "(* ---- END $SRC_NAME ---- *)"
  echo
} >>"$OUT"

append_file() {
  local rel="$1"
  local src="$ROOT/$rel"
  [[ -f "$src" ]] || die "Selected file missing at concat time: $src"
  printf "\n\n(* ---- %s ---- *)\n\n" "$rel" >>"$OUT"
  cat -- "$src" >>"$OUT"
}

for rel in "${SELECTED_FILES[@]}"; do
  append_file "$rel"
done

echo "Done. Wrote $OUT"
exit 0

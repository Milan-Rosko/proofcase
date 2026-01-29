#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Helper: collect extraction artifacts from the shadow build.
#
# - Locates the project root by finding _CoqProject
# - Ensures a shadow build exists (runs builders/1 compile.command if needed)
# - Copies extracted OCaml from scratch/shadow/witness into ./witness
# - Optionally snapshots assumption lines from the build log
# -----------------------------------------------------------------------------

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"

ROOT_CP="$ROOT/_CoqProject"
THEORIES_CP="$ROOT/theories/_CoqProject"

if [[ -f "$ROOT_CP" ]]; then
  COQPROJ="$ROOT_CP"
  ORIGIN="root"
elif [[ -f "$THEORIES_CP" ]]; then
  COQPROJ="$THEORIES_CP"
  ORIGIN="theories"
else
  echo "[extract] No _CoqProject found at:"
  echo "  - $ROOT_CP"
  echo "  - $THEORIES_CP"
  exit 1
fi

SHADOW="$ROOT/scratch/shadow"
WITNESS_SHADOW="$SHADOW/witness"
WITNESS_ROOT="$ROOT/witness"
BUILD_LOG="$ROOT/scratch/build.log"

RX_FILES="$(sed -e 's/\r$//' -e 's/[[:space:]]*#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$COQPROJ" | grep -E 'RX__.*\.v$' || true)"

echo "[extract] Using _CoqProject ($ORIGIN): $COQPROJ"
if [[ -n "$RX_FILES" ]]; then
  echo "[extract] RX files:"
  printf "  - %s\n" $RX_FILES
else
  echo "[extract] Warning: no RX__*.v entries found in _CoqProject."
fi

if [[ ! -d "$SHADOW" || ! -f "$SHADOW/Makefile.coq" ]]; then
  echo "[extract] No shadow build found; running builders/1 compile.command..."
  "$ROOT/builders/1 compile.command"
fi

if [[ ! -d "$WITNESS_SHADOW" ]]; then
  echo "[extract] No witness output found in shadow."
  echo "[extract] Ensure the RX exporter sets 'Set Extraction Output Directory "witness"'."
  exit 1
fi

mkdir -p "$WITNESS_ROOT"

if command -v rsync >/dev/null 2>&1; then
  rsync -a --delete "$WITNESS_SHADOW/" "$WITNESS_ROOT/" >/dev/null 2>&1 || true
else
  rm -rf "$WITNESS_ROOT"
  mkdir -p "$WITNESS_ROOT"
  cp -R "$WITNESS_SHADOW/"* "$WITNESS_ROOT/" 2>/dev/null || true
fi

if [[ -f "$BUILD_LOG" ]]; then
  grep -E "Assumptions|Axioms:|Parameters:|Closed under the global context" \
    "$BUILD_LOG" > "$WITNESS_ROOT/assumptions.log" || true
fi

echo "[extract] Extracted artifacts copied to: $WITNESS_ROOT"

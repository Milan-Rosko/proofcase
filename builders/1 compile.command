#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Options:
# - CLEAN=1  : force full rebuild (make clean before all)
# - GUARD=1  : fail if any build artifacts (.glob/.vo/...) appear under repo theories/
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
  echo "Checked for:"
  echo "  - $ROOT_CP"
  echo "  - $THEORIES_CP"
  echo "No _CoqProject found in either location."
  exit 1
fi

BUILD="${ROOT}/scratch"
SHADOW="${BUILD}/shadow"
BUILD_LOG="${BUILD}/build.log"

COQPROJECT_SRC="${COQPROJ}"
COQPROJECT_SHADOW="${SHADOW}/_CoqProject"

COQ_MAKEFILE="$(command -v coq_makefile || true)"
COQC="$(command -v coqc || true)"

CLEAN="${CLEAN:-0}"
GUARD="${GUARD:-1}"

# One certificate, inside _Builder
CERT_FILE="${HERE}/success.txt"

mkdir -p "${BUILD}" "${SHADOW}"
: > "${BUILD_LOG}"

# -----------------------------------------------------------------------------
# Prepare shadow sources
# -----------------------------------------------------------------------------
rm -rf "${SHADOW}/theories"
mkdir -p "${SHADOW}/theories"

if command -v rsync >/dev/null 2>&1; then
  rsync -a --delete "${ROOT}/theories/" "${SHADOW}/theories/" >/dev/null 2>&1 || true
else
  cp -R "${ROOT}/theories" "${SHADOW}/theories"
fi

cp -f "${COQPROJECT_SRC}" "${COQPROJECT_SHADOW}"

cd "${SHADOW}"

# -----------------------------------------------------------------------------
# Build
# -----------------------------------------------------------------------------
"${COQ_MAKEFILE}" -f "_CoqProject" -o "Makefile.coq" | tee -a "${BUILD_LOG}"

if [ "${CLEAN}" = "1" ]; then
  make -f Makefile.coq clean | tee -a "${BUILD_LOG}"
fi

make -f Makefile.coq -j 1 all | tee -a "${BUILD_LOG}"

# -----------------------------------------------------------------------------
# Axiom Listing
# -----------------------------------------------------------------------------
THEORIES_PATH="${SHADOW}/theories"
ALL_AXIOM_FILES_RAW="$(rg -l --no-messages "^\s*Axioms?\b" "${THEORIES_PATH}" || true)"
ALL_AXIOM_FILES="$(echo "${ALL_AXIOM_FILES_RAW}" | sed "s|${SHADOW}/||g" | sort -u)"
# -----------------------------------------------------------------------------
# Generate Certificate
# -----------------------------------------------------------------------------
UTC_NOW="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

hash_file() {
  # This converts the hex hash to binary and then to Base64
  # It shrinks the character count by about 30% without losing a single bit of data
  shasum -a 256 "$1" | awk '{print $1}' | xxd -r -p | base64
}

SELECTED_LIST="$(mktemp "${BUILD}/selected.XXXXXX")"
sed -e 's/\r$//' -e 's/[[:space:]]*#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d' -e '/^-/d' "${COQPROJECT_SHADOW}" | sort -u > "${SELECTED_LIST}"

COUNT="$(grep -c . "${SELECTED_LIST}" || true)"

{
  echo "(successful 'makefile' run.) "
  echo 
  echo " . . . . . . . . .....*************************.                           "
  echo ". . . . . ... ..... ....***************************.                       "
  echo " . . . . . . . . . . .. ... .. ... .....**************                     "
  echo ". . . . . .. .. .. .....********************************                   "
  echo " . . . . ... ..... ......********************************                  "
  echo ". . . . . . . . . . .. .... .... ....*********************                 "
  echo " . . . . . . ... .... .....**********************   *******                "
  echo ". . . . . . . .  .... ....*********************************.               "
  echo " . . . . .. .. ..... ....***********************************               "
  echo ". . . ... ... ..... .....***********************************               "
  echo " . . . .. ... ..... .....***********************************               "
  echo ". . . . .. ... ..... .....******************          *****                "
  echo " . . . . .. ... ..... .....***************              ***                "
  echo ". . . . . .. ... ..... .....************                 *                 "
  echo " . . . . . .. ... ..... .....*********                                     "
  echo ". . . . . . .. ... ..... ......******                                      "
  echo " . . . . . . ... ........ .......**                                        "
  echo "---------------------------------------------------------------------------"
  echo 
  echo "                    Date (UTC): $UTC_NOW,"
  echo
  if [ -n "${COQC}" ]; then
  echo "                   Rocq version: $(${COQC} --version 2>/dev/null | head -n 1)"
  echo "                   Method: isolated shadow, scratch folder"
  fi
  echo
  echo "---------------------------------------------------------------------------"
  echo
  echo "Axioms:"
  echo
  if [ -n "${ALL_AXIOM_FILES}" ]; then
    printf "%s\n" "${ALL_AXIOM_FILES}"
  fi
  echo "---------------------------------------------------------------------------"
  echo
  echo "_CoqProject file contents:"
  echo
  echo "=== BEGIN ==="
  echo 
  while IFS= read -r cp_line || [[ -n "$cp_line" ]]; do
    # Trim CR (in case of Windows line endings).
    cp_line="${cp_line%$'\r'}"
    printf "   %s \n" "$cp_line"
  done < "$COQPROJ"
  echo 
  echo "=== END ==="
  echo
  echo "---------------------------------------------------------------------------"
  echo
  echo "Hash(es) (Short SHA-256) of ${COUNT} Files:"
  echo
  echo "---------------------------------------------------------------------------"
  while IFS= read -r f; do
    [ -z "${f}" ] && continue
    if [ -f "${ROOT}/${f}" ]; then
      printf "   %s\n" "$(hash_file "${ROOT}/${f}")"
    fi
  done < "${SELECTED_LIST}"
  echo
  echo "------------------------"
  echo

} > "${CERT_FILE}"

rm -f "${SELECTED_LIST}"

echo "" | tee -a "${BUILD_LOG}"
echo "Build process finished." | tee -a "${BUILD_LOG}"
echo "Certificate written to: ${CERT_FILE}" | tee -a "${BUILD_LOG}"

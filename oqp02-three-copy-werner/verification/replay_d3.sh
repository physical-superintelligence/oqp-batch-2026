#!/usr/bin/env bash
# Exact replay of the d = 3 four-replica certificate (Zenodo record 23134454, version 1.1.0-candidate,
# doi:10.5281/zenodo.23134454; CC0 data, MIT code; mirrored at github.com/ipitchford/three-copy-werner-undistillability).
#   usage:  bash replay_d3.sh [workdir]      (default ./upstream_d3; the clone is 24 MB)
#   needs:  git; python3 >= 3.11 with numpy, scipy, sympy, python-flint;  about 4 minutes, 2.5 GB RAM
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${1:-$HERE/upstream_d3}"
REPO="https://github.com/ipitchford/three-copy-werner-undistillability.git"
COMMIT="66cd2f931abb1a2f24e18e1b86e280401be9a5e8"
DIGEST="57005a13ff0f4f829e48d545422156ae0e11d0dbd7fdec4dbd45cc43344de302"      # sha256 of the sorted list of (sha256, path) of the 776 tracked files of the copy we replayed
[ -d "$WORK/.git" ] || git clone --quiet "$REPO" "$WORK"
cd "$WORK"; git fetch --quiet origin || true; git checkout --quiet "$COMMIT"
echo "checked out $(git rev-parse HEAD)"
got="$(git ls-files | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1)"
[ "$got" = "$DIGEST" ] || { echo "content digest mismatch: $got"; exit 1; }
echo "content digest matches ($(git ls-files | wc -l) tracked files)"
OUT="$WORK/../replay_d3_out"; rm -rf "$OUT"
python3 -B -s certificate/verify.py --output "$OUT" --phase all --max-seconds 2400
python3 -B -s check_controls.py --replay "$OUT"
echo "expected: the verifier's last JSON line has \"status\": \"COMPLETE_PORTABLE_EXACT_CERTIFICATE_PASS\" and the controls print SEMANTIC_NEGATIVE_CONTROLS_PASS"

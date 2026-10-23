#!/usr/bin/env bash
# Exact replay of the d = 4 four-replica certificate of A.-X. Liu (github.com/GLiuax/d4-three-copy-werner).
# The repository states no licence of its own, so its data are not redistributed here: this script fetches it at
# the pinned commit, checks the content digest of all tracked files against the copy we replayed, and runs its
# five-stage exact verifier.
#   usage:  bash replay_d4.sh [workdir]      (default ./upstream_d4; the clone is 142 MB)
#   needs:  git; python3 >= 3.11 with numpy, scipy, sympy, python-flint;  about 7 minutes on two cores, 2 GB RAM
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${1:-$HERE/upstream_d4}"
REPO="https://github.com/GLiuax/d4-three-copy-werner.git"
COMMIT="2ba792faf30ba677b0b61ab319fa049ea002c307"
DIGEST="d4a3a3fba3c988f7669658ff90ff691b4f86ba7a42b6fbbff6f51058b4727544"      # sha256 of the sorted list of (sha256, path) of the 2510 tracked files of the copy we replayed
[ -d "$WORK/.git" ] || git clone --quiet "$REPO" "$WORK"
cd "$WORK"; git fetch --quiet origin || true; git checkout --quiet "$COMMIT"
echo "checked out $(git rev-parse HEAD)"
got="$(git ls-files | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1)"
[ "$got" = "$DIGEST" ] || { echo "content digest mismatch: $got"; exit 1; }
echo "content digest matches ($(git ls-files | wc -l) tracked files)"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 -c "import numpy, scipy, sympy, flint" || { echo "install: pip install numpy scipy sympy python-flint"; exit 1; }
for stage in reduction foundation rank "maps --workers 2" certificate; do
  echo "=== STAGE $stage  $(date -u +%FT%TZ)"
  python3 research/d4_independent_certificate_audit.py $stage
  echo "=== exit $?  $(date -u +%FT%TZ)"
done
echo "ALL FIVE STAGES EXITED 0: the d = 4 four-replica certificate verifies."

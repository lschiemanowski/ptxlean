#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

case "${1:-}" in
  "") ;;
  --clean) ;;
  *) echo "Usage: scripts/check.sh [--clean]" >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  echo "Usage: scripts/check.sh [--clean]" >&2
  exit 2
fi

# Lake selects the repository's lean-toolchain; reject an unexpected binary.
expected=$(sed -n 's|^leanprover/lean4:v||p' lean-toolchain)
actual=$(lake env lean --version)
if [[ -z "$expected" || "$actual" != "Lean (version $expected,"* ]]; then
  echo "Pinned Lean version mismatch: $actual" >&2
  exit 1
fi
echo "$actual"
python3 scripts/check_sources.py
python3 scripts/coverage_inventory.py
python3 scripts/check_worker_evidence.py
python3 scripts/test_coverage_inventory.py
python3 -m unittest discover -s tests -p 'test_worker*.py'
python3 scripts/check_proofs.py --scan
if [[ "${1:-}" == --clean ]]; then
  lake clean
fi
lake build

audit_log=$(mktemp)
trap 'rm -f -- "$audit_log"' EXIT
lake env lean Ptx/Audit.lean | tee "$audit_log"
python3 scripts/check_proofs.py --audit "$audit_log"
echo 'All source, build, and proof-dependency checks passed.'

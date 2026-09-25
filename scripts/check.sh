#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

clean=false
defer_form_ledger=false
for argument in "$@"; do
  case "$argument" in
    --clean) clean=true ;;
    --defer-form-ledger) defer_form_ledger=true ;;
    *) echo "Usage: scripts/check.sh [--clean] [--defer-form-ledger]" >&2; exit 2 ;;
  esac
done

# Lake selects the repository's lean-toolchain; reject an unexpected binary.
expected=$(sed -n 's|^leanprover/lean4:v||p' lean-toolchain)
actual=$(lake env lean --version)
if [[ -z "$expected" || "$actual" != "Lean (version $expected,"* ]]; then
  echo "Pinned Lean version mismatch: $actual" >&2
  exit 1
fi
echo "$actual"
python3 scripts/check_distribution.py
python3 scripts/check_sources.py
python3 scripts/coverage_inventory.py
python3 scripts/check_worker_evidence.py
if [[ "$defer_form_ledger" == true ]]; then
  echo 'Accepted-form ledger deferred: candidate replay requires coordinator revalidation before integration.'
else
  python3 scripts/check_implemented_forms.py
  python3 scripts/build_instruction_docs.py --check
  python3 -m unittest discover -s tests -p 'test_instruction_docs.py'
fi
python3 scripts/test_coverage_inventory.py
python3 -m unittest discover -s tests -p 'test_worker*.py'
if [[ "$defer_form_ledger" == true ]]; then
  echo 'Ledger regression fixtures use committed HEAD; candidate ledger refresh remains deferred.'
  PTXLEAN_LEDGER_FIXTURE_REV=HEAD python3 -m unittest discover -s tests -p 'test_implemented_forms.py'
else
  python3 -m unittest discover -s tests -p 'test_implemented_forms.py'
fi
python3 scripts/check_proofs.py --scan
if [[ "$clean" == true ]]; then
  lake clean
fi
lake build

audit_log=$(mktemp)
trap 'rm -f -- "$audit_log"' EXIT
lake env lean Ptx/Audit.lean | tee "$audit_log"
python3 scripts/check_proofs.py --audit "$audit_log"
echo 'All source, build, and proof-dependency checks passed.'

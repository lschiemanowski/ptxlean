# Accepted instruction forms

An accepted form is a particular spelling and operand contract, not an entire
instruction name. This ledger records only the four independently reviewed
forms `min.u32`, `max.u32`, `clz.b32` and `popc.b32`. Minimum and maximum compare
two unsigned 32-bit values. Population count counts one bits; leading-zero count
starts at bit 31. Their results are exact for all input bit patterns, including
zero. The broader instruction-section inventory remains unassessed.

Each record says which typed operands and predicate guards are represented,
which PTX version and hardware targets the manual permits, and where the actual
value definition, instruction execution, text conversion and universal proofs
live. A typed operand is an already classified register or value: this boundary
does not parse a complete PTX file or validate its register declarations. The
version and target conditions are reviewed source facts; the arithmetic decoder
does not enforce architecture eligibility. Source and destination may name the
same register because source values are read before the destination is written.

The ledger also lists uncovered sibling forms from the same four integer
instruction sections. A sibling is another type, width or modifier combination
for the same instruction. These entries explain missing signed comparisons,
packed values, saturation and 64-bit bit counts; they are not implementation
claims. Floating-point instruction sections and all other families lie outside
this selected ledger. No percentage or whole-section coverage follows from it.

Every accepted form points to the exact source section, accepted worker patch,
retained fresh-check result and independent review record. Local file hashes
pin the current definitions and proof locations as well as historical evidence.
The verifier rejects missing or changed referenced files, wrong source hashes or
anchors, missing declaration sites, duplicate forms and inconsistent acceptance
or patch references. Changing a referenced implementation requires reviewing and
refreshing its ledger entry rather than silently inheriting old evidence.

These checks establish traceability and detect stale records. They do not parse
Lean generally, rerun its kernel, prove source fidelity, or establish that the
current implementation equals an old worker patch. The normal Lean build and
dependency audit and independent semantic review remain separate requirements.
Historical replay evidence describes the accepted candidate at its recorded base;
it is not a new verification of every future foundation change.

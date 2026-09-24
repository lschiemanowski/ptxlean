# Accepted instruction forms

An accepted form is a particular spelling and operand contract, not an entire
instruction name. This ledger records fourteen independently reviewed forms:
`min.u32`, `max.u32`, `clz.b32`, `popc.b32`, `add.rn.f32`, `mul.rn.f32`,
`selp.b32`, `min.s32`, `max.s32`, `and.b32`, `or.b32`, `xor.b32`,
`not.b32` and `cnot.b32`.
The integer forms compare signed or unsigned words, count or combine bits, test whether a word is zero, or select a
word using a predicate, with exact results for all input patterns. The floating forms add or multiply encoded binary32 values
with nearest-even rounding and preserved subnormal values. Their result relation
keeps every non-NaN reference bit, including zero signs, and conservatively
admits NaN encodings; it does not assert that every such encoding is realizable.
The broader instruction-section inventory remains unassessed.

Each record says which typed operands and predicate guards are represented,
which PTX version and hardware targets the manual permits, and where the actual
value definition, instruction execution, text conversion and universal proofs
live. A typed operand is an already classified register or value: this boundary
does not parse a complete PTX file or validate its register declarations. The
older unsigned and bit-count decoders leave version and target checks to the
caller. Selection, signed min/max and the bitwise families use fetched steps requiring ISA 9.4 and
a numeric SM value of at least 10. The floating fetched-step interface requires
PTX ISA 9.4 and a numeric SM value of at least 20, preserving the source's
subnormal behavior; this does not validate target spellings or architecture
suffixes. Floating operands denote compatible `.b32`/`.f32` registers or exact
already-decoded `0f`/`0F` bit literals, not numeric conversions of integer operands.
Source and destination may name the same register because source values are read
before the destination is written. A floating leaf step does not prove complete
kernel execution.

The ledger also lists uncovered sibling forms from the selected integer and
floating instruction sections. A sibling is another type, width or modifier combination
for the same instruction. These entries explain missing widths, packed values, saturation and 64-bit
bit counts; they are not implementation
claims. Other floating rounding modes, flush-to-zero, saturation, packed and
64-bit forms remain outside the accepted floating slice. No percentage or
whole-section coverage follows from this ledger.

Every accepted form points to the exact source section, accepted worker patch,
retained fresh-check result and independent review record. Local file hashes
pin the current definitions and proof locations as well as historical evidence.
The verifier rejects missing or changed referenced files, wrong source hashes or
anchors, missing declaration sites, duplicate forms and inconsistent acceptance
or patch references. Changing a referenced implementation requires reviewing and
refreshing its ledger entry rather than silently inheriting old evidence.

Declaration locations use a bounded source scan that follows nested namespaces
(groups of Lean names), named or unnamed sections (local scopes), and their
matching ends. Relative qualified names are joined to the active namespace;
explicit root-qualified names start at the root. Comments and strings do not
create declarations. Missing or duplicate fully qualified sites and unsupported
scope syntax are rejected. This does not resolve aliases, expand macros or
identify generated declarations; private declarations are not public ledger sites.

These checks establish traceability and detect stale records. They do not parse
Lean generally, rerun its kernel, prove source fidelity, or establish that the
current implementation equals an old worker patch. The normal Lean build and
dependency audit and independent semantic review remain separate requirements.
Historical replay evidence describes the accepted candidate at its recorded base;
it is not a new verification of every future foundation change.

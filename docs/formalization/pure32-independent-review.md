# Independent review of the selecting integer leaves

This review reads the final candidate semantics and typed frontend against the
pinned PTX ISA 9.4 manual, separately from the coordinator's fresh reconstruction,
acceptance drivers, dependency audits and mutation probes. It does not change
or replace those archived trial receipts.

The pinned source is `references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.

For `Select32`, reviewed source SHA256 is
`4b8bc90df0d95d7f25a7e5d4512ad9f593466d5f1a008d1cf2c32214b9ea3152`.
Section 9.7.7.3 specifies selecting the first word when the predicate is true,
and the second when false. The candidate copies all selected bits and lowers
exactly two word operands and one positive predicate-register operand into the
shared `Pure32` execution mechanism. Both sources are evaluated in the incoming
state, so destination aliases are preserved. Selector and instruction guard
remain distinct. Both sources remain in syntactic read metadata; that metadata
is explicitly not a PTX semantic dependency claim. Only `selp.b32` and the exact
four-token typed form are decoded. Wider, signed, floating and other selector
forms remain outside the accepted slice. The instruction was introduced in
PTX 1.0; the section's extra target restriction concerns only `.f64`.

For `SignedMinMax32`, reviewed source SHA256 is
`651f4d1c2b73916b3269e72257f327e0259dff2310512b6ab1b0f65b8b17bbb2`.
Sections 9.7.1.13 and 9.7.1.14 compare signed operands with strict less-than or
greater-than and choose the second operand on equality. The candidate compares
`Word.toInt` and returns the original operand bits. Its universal `compute_toInt`
theorem connects the output to integer min/max for all words, including the
most negative representable value. No saturation or exceptional minimum-integer
case is introduced. The exact `min.s32` and `max.s32` decoders exclude `.relu`,
packed, unsigned and wider sibling forms. The plain scalar forms have no extra
architecture threshold in these sections.

Both leaves use the shared guarded evaluator and fetched-step relation. Enabled
steps write the selected destination and advance the PC; skipped steps preserve
data and still require a supported fetched instruction. The original leaf is
recovered from the actual program lookup. Existence, deterministic results,
frames and decoder inverse statements introduce no output-equality assumptions.
The numeric target predicate `isa = 94` and `sm >= 10` is a selected feature
boundary, not validation of every real target spelling or modern assembler
support for historical architectures. Register declaration compatibility,
raw parsing/literal conversion and whole-program termination remain external
to this typed leaf layer. No review blocker was found.

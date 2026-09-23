# Reading the PTX instruction-section inventory

`coverage/ptx-isa-9.4-sections.json` records every section inside **9.7,
Instructions**, of the locally pinned NVIDIA manual. It currently partitions
451 sections into 219 instruction sections, 81 grouping sections, 149 explanatory
sections and two language constructs (`{}` and `@`). These numbers describe the
manual's organization. They are **not a percentage of PTX implemented**.

The extractor uses only Python's standard library and reads no network resource:

```sh
python3 scripts/coverage_inventory.py          # verify the committed JSON exactly
python3 scripts/test_coverage_inventory.py     # extraction and boundary regressions
python3 scripts/coverage_inventory.py --write  # regenerate after a reviewed change
```

The source must match the version, byte length and SHA-256 hash in
`references/nvidia/ptx-isa-9.4/manifest.json`. Each entry records its HTML anchor,
heading, parent, source lines, byte offsets and source URL. Byte offsets are
zero-based, with an exclusive end; the section hash covers the original UTF-8
bytes from the opening `<section>` through its closing tag, including children.
Line numbers are one-based. Hashes identify content, not its correctness.
Generation is deterministic: there are no timestamps or model-generated fields.
The default command compares exact serialized contents, so an edited or stale
inventory fails verification.

## Why this is a section count

A heading naming an instruction is not a complete task specification. `add` has
separate integer, floating-point and other sections. Two sections are both named
`mov`; their anchors distinguish them. Conversely, a single section may cover
several names, such as `prefetch, prefetchu`. A name can combine with multiple
operand types and options, with restrictions on their combinations. Version and
hardware conditions also affect which combinations are permitted. Those are
instruction **forms**, and this inventory does not enumerate them.

The extractor classifies leaf headings of the form `Instruction(s): mnemonic`
as instruction sections, allowing explicit lists and deprecated names. Headings
with nested sections are retained as groups, including the enclosing `mbarrier`
object discussion. Individual operations such as `mbarrier.init` are separate
instruction sections. Background material such as matrix layouts, cache hints,
and completion mechanisms stays in the inventory but outside the instruction
count. Predication (`@`, conditionally executing an instruction) and block syntax
(`{}`) are recorded as language constructs rather than instruction names.

This classification follows the pinned document's heading convention; it is not
a general parser for future manual formats. Every section in the chapter is
retained, including grouping and background sections. Missing headings, duplicate
anchors or numbering, unnumbered sections, inconsistent nesting, and unrecognized
instruction-heading spellings fail extraction instead of disappearing silently.
Regression tests independently enumerate the source chapter's section tags and
check important exceptions. Source changes require renewed review of the
classification policy, not just updating the expected counts.

## What work remains before claiming coverage

Every instruction entry starts with `form_coverage: not_elaborated` and
`implementation_coverage: not_assessed`. The latter does not mean the project has
no existing restricted instruction support. It means this inventory has not
mapped that support to the complete source section. Name matching would give
misleading credit, so the extractor does not inspect Lean names at all.

Before delegating a task, a reviewed task package must identify a bounded set of
forms, their exact source passages, exceptional behavior, required shared
foundations, and required proofs. Later evidence must distinguish assignment,
submitted definitions, checked proofs, independent semantic review and integrated
results. Those records belong beside this reproducible source inventory; do not
hand-edit generated rows to award coverage. This first artifact is a source
inventory, not the completed workflow ledger.

The full PTX release also needs computing-model coverage beyond section 9.7:
thread and memory organization, types, instruction-wide rules, directives and
other obligations. Even perfect accounting of every row here would not establish
that coverage, hardware conformance, or semantic fidelity. The finite counts
provide a starting point for assigning source work without hiding the much
larger question of which instruction forms and interactions have been proved.

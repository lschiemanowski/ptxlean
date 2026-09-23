# Instruction-section inventory

Before instruction formalization is delegated, the project records which parts
of the pinned PTX 9.4 manual describe instructions. Each entry identifies a
section by its stable HTML anchor, heading and parent, and locates its exact
source bytes. A cryptographic hash identifies the source document and each
section, so a worker's assignment can be tied to the text that was actually
reviewed. Rebuilding the inventory from the same source produces identical data.

Every section within the manual's Instructions chapter remains visible. Sections
that specify instructions are distinguished from headings that group them,
background explanations and language constructs such as conditional execution.
Only instruction sections enter the instruction-section count. Multiple sections
may describe the same instruction name, and one section may describe several
names. Neither section counts nor name counts measure supported instruction forms.

An instruction form combines the instruction name with operand types, options,
version requirements and hardware conditions. Those combinations require a
separate source review before work is assigned. The inventory marks every
instruction section as needing that elaboration and makes no claim that its
forms have been implemented, proved or accepted. Existing restricted instruction
support is not promoted to full-section coverage by matching names.

The inventory checks that the source matches its pinned manifest, that section
identities and headings are unambiguous, and that every section in scope is
accounted for exactly once. Tests exercise classification boundaries and reject
missing, duplicate or malformed source structure. These checks establish the
provenance and completeness of the extracted section list relative to this HTML
chapter; they do not establish completeness of the PTX formalization or fidelity
of instruction semantics. Computing-model chapters outside this inventory remain
independent semantic obligations.

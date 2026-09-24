# Semantic fidelity

Semantic fidelity means that the formal definitions express the behavior NVIDIA
documents. Each interpretation connects a passage from a specified version of
the manual, including its qualifications, to a plain-language explanation, formal
rules, and permitted and forbidden examples. Ambiguities and choices remain
visible so that another reader can review and reproduce the interpretation.

Source review checks NVIDIA's guarantees, exceptions, cases where it leaves
behavior undefined, PTX-version requirements, and restrictions on supported GPUs.
Internal adequacy results prove that pieces of the formal model fit together,
that suitable programs have executions, and that derived proof rules follow from
the foundation. Small programs designed to distinguish memory behaviors, called
litmus tests, and hardware experiments provide additional evidence for finding
mistakes. Such experiments are not general proofs that hardware obeys the model.

Model-assisted formalization delegates instruction definitions and proof
candidates to smaller models using shared, reviewed semantic foundations.
Each task supplies the source passages, fixed interfaces and acceptance obligations
for a bounded instruction family. The coordinator develops those foundations,
maintains coverage, and evaluates the generation and review workflow; routine
instruction-by-instruction expansion belongs to the delegated workers.
Lean checks submitted proofs, while source review and
independent checks address whether their definitions describe the intended
behavior. Generation records identify the inputs, outputs, checking results,
and costs needed to assess reproducibility and cost effectiveness. A generator
agreeing with its own definitions does not establish semantic fidelity.

The explanation of a rule states which parts of its justification come from
source interpretation, checked theorems, assumptions, or experiments. These
explanations also provide material for studying the computing model.

Reproducible integration checks verify the pinned Lean toolchain and the exact
Git revisions of numerical dependencies, rejecting changed tracked dependency
files. They build the selected PTX–TorchLean integration targets, reject local
proof placeholders and unchecked axioms, and freshly inspect the named theorem
and definition dependencies. The requested audit list must match the reported
list exactly, and only Lean's standard logical axioms are accepted. Source and
configuration hashes are checked before and after the run. These checks establish
what was built and which formal dependencies were used; they do not turn a
software arithmetic model into a hardware-conformance proof or resolve an
ambiguous source contract.

Vendor documentation is acquired locally from its publisher, not bundled with the
project. Committed URLs, version identifiers, section locators and hashes identify
the reviewed source. Source checks require exact bytes and reject a changed or
missing document; they do not silently replace the reviewed version. Public
evidence retains project-authored contracts, patches and check results while
omitting raw model transcripts that can contain copied vendor passages. Omission
records preserve the original member hashes and make the reduced evidence scope
explicit. Git history and release artifacts need the same distribution boundary.

A distribution guard can inspect the current tracked files or every commit
reachable from a selected publication revision, including evidence archive
members. It rejects known manual artifacts and raw model event transcripts.
This is a check for those artifact types, not an exhaustive audit of quotations.
Private recovery bundles and local caches are outside the published history.

# Model-assisted instruction formalization

Smaller models expand instruction coverage by producing definitions, proofs and
explanations for bounded instruction families. They work against shared semantic
foundations: the representation of values, thread state, memory effects, ordering
and execution outcomes. The coordinator develops and reviews these foundations,
prepares tasks, evaluates workers and integrates accepted results. A worker that
needs a missing foundation reports that dependency instead of inventing a local
replacement or assuming its behavior.

## What a worker receives and returns

A task package identifies the pinned PTX source passages, instruction forms,
operand types, options, version and hardware conditions, and permitted files to
change. It supplies the existing Lean interfaces and the required theorem
statements. A task states whether the coordinator supplied the computation body
or the worker must derive it from source. In the latter case, independent
source-derived properties constrain the result without prescribing its
implementation; checks are frozen before generation. Preparation of those
properties, reference fixtures and checks remains coordinator work. A source-derived obligation lists what a result must preserve,
including permitted multiple outcomes and behavior for which the manual gives
no guarantee. An instruction family is not covered merely because its main
instruction name appears in a definition.

Before dispatch, the coordinator exercises the complete acceptance checks on a
separate reference fixture and checks that deliberately wrong results are rejected.
This catches errors in checking code before a task is frozen. Reference fixtures
are excluded from worker inputs and are recorded as coordinator effort; passing
these checks does not establish that the chosen contract matches PTX. Any later
checker repair is retained and reported separately from worker repairs.

The returned package contains the proposed definitions, completed proofs,
source-to-definition explanation, boundary examples and unresolved questions.
Proofs refer to the shared foundations. Workers cannot make their task easier
by changing those foundations, weakening required theorem statements, replacing
undefined behavior with convenient deterministic behavior, or dropping difficult
forms from their assigned scope. Such proposals require a separate reviewed
change and remain visible in the task result.

## Two kinds of acceptance

Mechanical checks establish that the submission builds with the pinned Lean
version, has no proof placeholders or new unchecked axioms, obeys its edit
boundary, and preserves required interfaces and previous results. Theorem
assumptions are inspected: a proof that assumes the desired result does not
satisfy the task. Tests and examples exercise ordinary behavior, exceptional
cases and rejected forms.

Semantic review separately compares the definition with the source obligations.
A reviewer other than the generating worker checks the meaning of operands,
conditions, allowed outcomes and interactions with the computing model. The
review uses independently prepared expectations and distinguishing examples;
agreement between models alone is insufficient. Deliberately faulty submissions
check whether the review process detects important mistakes. Such checks measure
review quality; they do not prove all semantic errors impossible.

When semantic review is delegated to an inexpensive model, it is a separate
review task from generation. The reviewer receives the pinned source obligations,
the candidate and independently prepared checks, and returns an explanation of
source correspondence, counterexamples and unresolved questions. Its verdict
cannot replace Lean checking or authorize integration by itself. The review
mechanism is evaluated with deliberately incorrect candidates before relying on
it to expand coverage; agreement between generator and reviewer is not evidence
that an ambiguous source interpretation has been resolved.

Only submissions passing both kinds of review enter the accepted formalization.
An unresolved source interpretation is recorded as such, with any conditional
results stated explicitly. Passing Lean checking alone never promotes it to a
faithfully covered instruction. Integration reruns the relevant checks against
the combined project, since individually accepted changes can interact.

## Coverage and evaluation

A coverage ledger lists the instruction families and their forms against the
pinned manual. It distinguishes missing prerequisites, unassigned work, generated
submissions, checked proofs, completed semantic review and integrated results.
A missing form remains visible; accounting for it does not implement it. Updates
to a shared foundation invalidate dependent results until the required checks
and reviews are repeated.

Exploratory evaluation asks which tasks workers can complete and what assistance
they need; prompts and feedback may change while those attempts remain recorded.
A later productivity evaluation asks how much accepted work a fixed workflow
produces for the effort spent. It separates tasks used to improve prompts from
held-out tasks reserved for measuring the frozen workflow. Closely related forms are grouped to avoid
treating near-duplicates as independent evidence. Reports include every assigned
task, failed and interrupted attempts, repairs and reviewer interventions. They
separate first-attempt proof checking, eventual acceptance, semantic rejection
and unresolved cases, and do not generalize a narrow sample to the full ISA.

Each run records its source and repository revisions, task package, requested
and reported model identity, settings, tool actions, patches, check results and
review decisions. Stored outputs can be checked again without another model
call; regeneration is not promised to reproduce the same text. Run policies distinguish exploratory work from evaluations with fixed budgets.
They record any retry, time or usage limits and campaign check-in points; a
missing per-task limit is not invented as an acceptance condition. Spending and review effort are reported
per accepted task as well as in total, including unsuccessful work and repairs.
Missing usage or billing data remains unknown rather than counted as zero.

The workflow can be evaluated with a configured smaller model without making
that model part of the PTX semantics. Changing the worker, prompt, task interface
or reviewer produces a new evaluation condition. Model-assisted expansion does
not automatically generate neural-network PTX backward code or its correctness
proof; that is a separate project responsibility.

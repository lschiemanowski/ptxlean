# Proposed release contract: PTX foundations, delegated coverage and verification infrastructure

**Status: release criteria remain a draft; the user has selected Codex headless for exploratory Luna runs, with a check-in before exceeding 200 calls. This is not a completion report.**
The project target remains full PTX ISA 9.4 and reusable TorchLean–kernel
verification. Gemma's implementation and proofs are deferred; its description
remains part of the longer-term project. No new Lean implementation or model
evaluation is delivered by this document.

The coordinator's main work is the computing model, shared instruction interfaces,
verification infrastructure, and a measured workflow for delegating instruction
formalization. Smaller models, initially GPT-6 Luna, do the routine expansion of
instruction definitions and proofs. A few coordinator-developed reference cases
establish conventions and test the interfaces; they are not a plan to manually
formalize every instruction.

Two milestones must not be conflated:

- **Foundations and workflow ready:** representative instruction families and
  verification examples work, the handoff and review process has been evaluated,
  and every remaining coverage item is tracked. This is an intermediate release.
- **Non-Gemma target complete:** all the criteria below pass, including the
  delegated full-coverage campaign. A pilot, a list of unsupported instructions,
  or a broad but uninterpreted interface is insufficient for this claim.

The enduring responsibilities are in [Stratic](../../stratic/descriptions/root.md),
including [model-assisted instruction formalization](../../stratic/descriptions/model-formalization.md).
The candidate examples, pilot sizes and operating limits here are release choices,
not permanent statements of PTX semantics.

## Division of work

| Responsibility | Coordinator | Smaller-model workers |
| --- | --- | --- |
| Computing model | Develop state, values, memory, concurrency, synchronization and asynchronous execution foundations; justify consequential choices against the source. | Identify missing facilities while attempting assigned work; do not invent substitutes. |
| Instruction interface | Define how operands, effects, permitted outcomes, version restrictions and proofs connect to the foundation; supply a small set of reviewed reference implementations. | Implement assigned families through that interface, with proofs and explanations. |
| Semantic accuracy | Establish review obligations and independently check source interpretations and consequential interactions. | Return source-linked reasoning and examples; report ambiguity or inability to finish. |
| Integration | Maintain coverage, test combined changes, resolve shared design issues and keep Stratic aligned. | Return isolated, reproducible patches within assigned boundaries. |
| Evaluation | Build the runner, frozen task suites, review tests and complete reports; measure accepted work and total cost. | Participate in bounded generation and repair runs with preserved records. |
| Network verification | Develop TorchLean connections, numerical contracts, orchestration and backward verification infrastructure. | Assist on bounded implementation/proof tasks when suitable; automatic TorchLean differentiation does not itself generate PTX backward kernels. |

## Completion criteria

| Area | Evidence required to call it complete |
| --- | --- |
| PTX coverage accounting | A source-linked inventory covers instruction families, documented operand/type/option combinations, target and version conditions, and relevant module/execution conditions. Structured rules may represent combinations; mnemonic counts alone are insufficient. Every item has an accountable status. |
| Computing model | Represented execution covers the thread groups, storage/addressing, dependencies, memory ordering, synchronization, atomics, collective operations and asynchronous operations needed by the pinned instruction inventory. Necessary conditions are explicit. Features requiring additional state have implemented transitions and validity rules, not only names or uninterpreted predicates. |
| Generated instruction coverage | Every in-scope form is connected to the shared semantics and has completed mechanical checks and semantic review. Illegal combinations and documented undefined behavior are distinguished from missing support. Source ambiguity has an explicit resolution or a qualified conditional account; an unresolved choice prevents claiming an unqualified faithful account of the affected behavior. |
| Reusable kernel verification | Instruction steps compose into kernel contracts. Read observations remain connected to actual register computations and memory effects. Representative results distinguish correctness on completion, existence, safety and termination; no general scheduler or hardware progress claim is inferred from one terminating schedule. |
| TorchLean interface | Pin and inspect the actual upstream library, identify supported definitions and derivative theorems, and build against it. Relate tensors and persistent state to memory, with layout, ownership and precision conditions. An independently recreated toy network language is not a completed TorchLean integration. |
| Multiple kernels and state | Prove composition through intermediate storage and persistent state, including access, lifetime, ordering and visibility conditions. State the runtime contracts explicitly; proving those contracts for CUDA or a physical GPU is a separate claim. |
| Numerical accuracy | Specify formats, rounding, accumulation order, conversions, exceptional values and permitted approximations. Prove error results covering all allowed outcomes on explicit input domains. Compose forward and derivative bounds and distinguish them from exact bitwise correspondence. Show concrete bound magnitudes for examples. |
| Backward verification | Use checked automatic TorchLean backward construction for weighted output derivatives, the vector-Jacobian interface. Verify separately supplied PTX backward code and its execution properties. Mathematical differentiability, backward correctness, numerical error and execution existence/termination remain separate results. |
| Concrete Torch/PyTorch correspondence | Pin the reference version, configuration and computation path for examples. Separate mathematically proved correspondence to an explicit numerical specification from measured agreement with PyTorch. An unverified backend or compiler link stays an assumption or testing boundary. |
| Reproduction and explanation | Clean builds, source hashes, dependency audits, evaluation records, coverage reports and examples reproduce the stated results. Stratic explains contracts and consequential choices; guides supply extended worked examples. Each milestone has coherent commits and a short review account. |

Full coverage includes the less convenient instruction families. They can wait
for their prerequisites, but cannot disappear from the completion denominator.
Current semantic questions remain release obligations: preventing read values
from being justified only by circular dependencies; deciding how mixed-byte reads
count as observing writes; and extending memory beyond aligned equal-size accesses.
The inventory must identify affected families and conditional results explicitly.
Hardware conformance and arbitrary compiler preservation are not assumed release
achievements. Likewise, the current small word-memory model must not be promoted
to full PTX merely by placing more instructions over it.

## Finite examples that exercise the reusable interface

These are proposed acceptance examples, not additional large model projects:

1. **Computed-data publication:** actual scalar loads, arithmetic and a
   register-derived store, followed by release/acquire communication; universal
   completed-result guarantee, execution witness, safe accesses and a relaxed
   stale-read counterexample.
2. **Cooperating threads:** a small shared-memory reduction using a barrier,
   which makes participating threads wait at a coordination point. Prove the
   required participation and ordering conditions; do not infer hardware fairness.
   Add separate distinguishing tests for atomic and asynchronous foundations as
   those are introduced.
3. **A small differentiable network:** an affine layer and a differentiable
   activation, with a vector-Jacobian interface and one concrete scalar loss.
   Use automatic TorchLean backward construction, separately authored forward
   and backward PTX, and numerical and execution proofs. Keep dimensions
   parameterized where feasible. A squared-error loss is the proposed first
   example; it does not remove the later Gemma loss requirements.
4. **Storage, precision and composition variants:** implement a network example
   through multiple kernels, exercise two tensor layouts, and verify an explicit
   persistent-state update across calls. Demonstrate saved forward values and
   recomputation in backward verification. Provide a single-format case and a
   mixed-format case; proposed initial cases are FP32 and BF16 storage with FP32
   accumulation, subject to the verified upstream and numerical foundations.

Example format choices do not settle Gemma's numerical policy or reduce the
full-ISA format target. The release needs concrete proofs, not only generic
contracts parameterized by an assumed correct kernel. If upstream TorchLean
lacks a required operation or theorem, record the exact extension needed and
implement or explicitly resolve it; do not assume that the capability exists.

## Worker workflow and semantic evaluation

Start with the smallest runner that can package a task, execute it in an isolated
checkout, collect a patch and receipts, and replay checks without a model call.
A fake worker and stored responses exercise interruption, failure, retry and
resume paths before any live pilot. Use stable task identifiers so a restart
does not silently repeat completed billable work.

Each task fixes the source hashes and passages, prerequisite revisions, allowed
files, interfaces, theorem obligations and resource limits. Workers can report
missing prerequisites or ambiguity. A worker must not change acceptance checks,
shared semantics or required theorem statements to obtain a pass. A justified
foundation change is handled separately and triggers dependent checks.

Acceptance has separate stages:

1. Check the edit boundary, source provenance, build, completed proofs and theorem
   dependencies. Reject new unchecked axioms, proof placeholders, circular
   correctness assumptions and unapproved contract changes.
2. Compare the meaning with obligations prepared from the manual independently
   of the generated definition. Review conditions, types, ordering, exceptions,
   allowed multiple results and target restrictions. Model agreement alone does
   not establish fidelity.
3. Exercise distinguishing examples and independent calculations where available.
   Use permitted and forbidden cases. Hardware experiments remain supporting
   evidence, not a universal semantics proof.
4. Review and integrate the exact patch, update Stratic and coverage, then rerun
   affected checks on the combined tree. Keep rejected and unresolved submissions.

### Exploratory capability study first

The first question is whether Luna can produce semantically correct instruction
formalizations and completed proofs with useful task packages and feedback.
There is no initial minimum success percentage, fixed per-task repair count,
token cap or short task deadline. The coordinator may improve prompts, foundations
and feedback while learning what works, preserving the sequence of attempts.
Repeated lack of progress warrants diagnosis, not an automatic blind retry.

Begin with a small, varied set of families whose semantic foundations are ready,
then increase difficulty. Distinguish failures caused by missing foundations,
poor task packaging, proof difficulty, semantic misunderstanding and runner
problems. Report first-attempt success separately from success after assistance.
Record exactly how much semantic design or proof repair the coordinator supplied;
completion after effectively supplying the solution is not evidence of independent
worker capability. Infrastructure-only failures do not measure formalization
ability, but remain in the attempt and usage records.

A useful result is a set of fully reviewed examples plus an honest account of
which tasks Luna can handle, with what help, and where it fails. Strict proof
and semantic acceptance still apply to every accepted artifact. Adaptive work
is exploratory evidence, not an unbiased success-rate estimate. No model calls
have been made as part of drafting this contract.

### Later frozen evaluation, if capability warrants scaling

Use a development set for prompt and tooling changes, then freeze a separate
set of **24 held-out tasks**, with four tasks in each of six groups: integer/bit
operations; floating-point/conversion operations; memory/addressing; atomics;
synchronization/asynchronous operations; and vector/collective/matrix operations.
Tasks are bounded families or forms with their prerequisites already reviewed.
Group closely related families into one split so near-duplicate variants do not
leak between development and evaluation. A group blocked on its foundations stays
reported as blocked; it is not quietly replaced with easy integer tasks.

A possible later design is two independent attempts of the frozen suite, with
a fixed repair allowance chosen before those runs. This is not a repair limit
on the exploratory study. Review expectations and held-out
answers are not given to the generator. A pilot exposed to prompt tuning becomes
development data; evaluation then needs a fresh held-out suite.

A productivity threshold would specify how much accepted work must be produced
for a chosen amount of model and review effort. The earlier draft suggested
18 of 24 accepted tasks with at most two repair rounds after the initial attempt,
plus a minimum result in each group. That threshold is withdrawn as an initial
gate: it answered whether a workflow is ready to scale, whereas the first study
asks whether it can work and what support it needs. Choose any later scaling
threshold from the capability evidence, and freeze it before the evaluation
used to test that threshold. A failed threshold never permits weaker correctness
criteria or deletion of difficult tasks from a report.

Also freeze faulty submissions covering wrong signedness, boundary shifts,
rounding, missing target conditions, lost memory ordering, unjustified single
outcomes and weakened theorem hypotheses. Include defects that still compile
and prove against their own wrong definitions. Require rejection of every
must-detect seeded defect before scaling; report false rejections on correct
controls and any undetected defects. This tests the evaluation process itself.

Measure first-attempt build/proof success, eventual semantic acceptance, failures
by cause, repair counts, unresolved cases, review effort, elapsed time and total
model usage. Report every assigned task in the denominator. Include unsuccessful
attempts, repairs, reviewers and coordinator interventions in the cost account.
Show cost and review effort per accepted task, with raw counts by family and
uncertainty across repetitions. No cost-effectiveness claim follows just from a
high proof-checking rate or a model's published token price.

Held-out evaluation and explicit criteria are consistent with OpenAI's
[evaluation guidance](https://developers.openai.com/api/docs/guides/evaluation-best-practices).
The PTX-specific source review, proof audit and seeded-defect gates above are
project requirements, not claims that a general model grader can certify semantics.

### Model configuration and operating limits

The initial requested worker is GPT-6 Luna. The official
[model page](https://developers.openai.com/api/docs/models/gpt-6-luna) identifies
`gpt-6-luna`; account access and suitability for these tasks are not established
by that documentation. The selected route is Codex headless, using the existing
Codex account. OpenAI documents [`codex exec`](https://learn.chatgpt.com/docs/non-interactive-mode)
as its non-interactive CLI route. Verify local CLI support and Luna availability
before launching work; do not substitute a model silently.
Record the requested model, returned identity/version when exposed, settings and
run date; do not claim an immutable model snapshot when only an alias is available.
Retain exact prompts, tool actions, outputs and repository patches for replay.

The user's current instruction authorizes exploratory use of the selected Codex
headless route. It does not authorize switching to separately billed API calls,
buying credits or using a different provider. There is no fixed dollar budget or
per-task productivity cap for this exploratory phase.

**Campaign checkpoint: check back before launching call 201.** Count every
model-running headless invocation in this capability campaign, including initial
worker calls, repair/resume calls, retries and separate headless reviewer calls,
even when an invocation fails or is interrupted. Local checks and commands such
as `codex --help` do not count. One invocation can contain many model turns and
tool actions; those are not separate headless calls, but their reported usage
and elapsed time must still be recorded. This is a limit on further dispatch
until discussion, not a requirement to consume 200 calls or truncate a useful
run arbitrarily. Give an earlier update if progress stalls or the approach needs
a substantive change. Do not reset the count when changing prompts or tasks.

Use the normal configured execution safeguards without introducing arbitrary
short inference or repair limits. Record cumulative calls, tokens and account
usage when exposed, wall time, task outcomes and review effort. Do not manufacture
dollar costs for account usage. Missing usage fields remain unknown. Retain
outputs for checking without repeat inference; do not stretch individual calls
into hidden campaigns to evade the checkpoint.

## Autonomous milestones and decision boundaries

1. **Coverage and foundation audit:** build the inventory and dependency map;
   identify the common interfaces and exact unresolved semantic obligations.
2. **Reusable execution connection:** complete computed-data publication and
   generalize only the machinery needed by it; preserve earlier examples.
3. **Delegation runner and capability study:** implement packaging, replay,
   review and failure handling; explore ready families using Luna via Codex
   headless. Assess capability and assistance needs first. Consider a frozen
   evaluation for scaling only afterward, as the relevant foundations mature.
4. **Computing-model and numerical expansion:** develop shared foundations for
   the remaining families, including synchronization and asynchronous state;
   alternate foundation work with evaluated instruction batches.
5. **TorchLean and network verification:** pin upstream, deliver the concrete
   acceptance examples, composition and backward infrastructure. Start upstream
   investigation early so missing capabilities are discovered before integration.
6. **Coverage closure and release audit:** run the remaining delegated campaign,
   review all claimed coverage and reproduce the full result. Report exact
   blockers if the non-Gemma completion criteria are not achieved.

These milestones organize review; they do not require permission for every
routine edit. The coordinator chooses representations, helper lemmas, module
boundaries and bounded example details, documenting consequential choices in
Stratic. Each completed block records what changed, why, checks performed and
remaining obligations. The original project ambitions remain intact.

A source ambiguity that changes permitted executions, an unsupported upstream
capability that changes the promised interface, a proposed reduction of coverage,
or a new spending requirement needs a concrete decision. Isolate the obligation,
propose alternatives and continue independent work. Do not hide the obstacle in
an assumption, choose a stronger hypothesis merely to finish a proof, or declare
a conditional fragment to be full PTX.

**Operating choices now settled:** Codex headless with Luna; an exploratory
capability study rather than an initial productivity gate; no arbitrary
per-task inference or repair cap; check back before exceeding 200 headless calls.
The later scaling threshold remains to be chosen from evidence. The example
precision choices above are proposed defaults for infrastructure validation
only; no Gemma precision choice is needed to begin foundation work.

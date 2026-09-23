# Independent review of mixed scalar execution

Reviewed source: [PtxBinary32/Mixed.lean](../../integration/torchlean/PtxBinary32/Mixed.lean),
SHA-256 `290857352333ca9e27901f1e02933b514a0e020d9695cf9276db2d4d1499589f`.
The implementation author reported this API stable before the review. The
reviewer made no proof-code changes.

## Instruction and fetch correspondence

`Eval.scalar` lifts exactly `Scalar.eval none`: the existing predicates, local
arena reads, writes, branches, unsupported results, faults and exit retain their
original meanings. It does not replace a scalar result with an arbitrary
observation. `Eval.binary32` lifts exactly `Scalar.Binary32.Eval` and preserves
the floating-point occurrence tag. Both directions are exposed by the evaluator
characterization theorems. Floating-point steps can only advance; they cannot
fabricate a scalar halt, fault or unsupported result.

`Dispatch` fetches `program[s.pc]?` and requires the stated ISA94/sm70 feature
slice. A missing instruction produces the existing invalid-PC fault. An
unsupported target has no admitted dispatch. Neither mechanism is claimed to
model a hardware exception. The stronger sm70 condition implies the sm20
condition of the FP instruction layer. Numeric target thresholds are not a
validator for full target names.

`eval_event_origin` and `dispatch_event_origin` derive event position and exact
instruction identity from the underlying evaluation and fetch. The event label
is not an independent premise that could describe a different instruction.

## Prefixes, terminal outcomes and existence

`Path` describes a finite advancing prefix; its empty constructor says only that
zero steps have occurred. `Run` instead requires a final actual dispatch with
one of three terminal outcomes: halt, fault or unsupported. `Run.not_exhausted`
excludes fuel exhaustion. A halted run retains its actual exit event; a fault or
unsupported result retains the current state and contributes no successful
event. The constructors do not silently turn out-of-range fetch into exit.

`dispatch_exists` proves a next or terminal outcome for one dispatch at an
eligible target. It uses the existing nonempty numerical result relation for
FP steps. It is not a termination theorem for arbitrary programs, and no such
claim is made by the description. The scalar and FP run inversion theorems
retain the actual fetched instruction, intermediate state and remaining run.
The FP inversion is explicitly for an enabled guard; general `Eval` still
includes skipped FP instructions. No finite-result or successful-output premise
is added.

## Safety and frame contracts

For every advancing step, `eval_next_safe` derives unchanged arena length and
valid addresses for every emitted memory effect. Scalar accesses inherit the
actual scalar alignment/bounds checks. FP events have no memory effect and leave
the memory list unchanged. A halted step leaves the state unchanged and has no
memory effect. The corresponding dispatch, path and run theorems lift these
facts, including successful events before a later fault.

The safety result is not a promise that every attempted address is valid: an
invalid scalar access can fault and emits no successful memory event. It does
not establish runtime allocation permissions or address translation.

`StoresTo` examines the actual emitted memory effect, its store kind and its
resolved word index. The frame theorems assume only that no recorded store
writes the queried slot. They then derive equality of initial and final optional
word lookups. This premise identifies the footprint to preserve; it does not
assume the desired preserved value. There is no additional numerical-value,
source-identity, memory-validity or nonalias premise hidden in the proof.

## Scope and independent checking

The slice uses one sequential scalar state and concrete reads from its current
word arena. Isolation from other threads, host actions and asynchronous work is
an interpretation boundary. The module does not claim admission under general
PTX concurrent memory semantics, hardware progress, memory permission checking,
raw PTX parsing or exact hardware realizability of the conservative NaN set.
The original numerical relation remains unchanged and universal run reasoning
must cover all of its admitted results.

Fresh source elaboration from the pinned integration project passed:

```text
lake env lean PtxBinary32/Mixed.lean
```

It produced only style warnings about tactic spelling at lines 153 and 198.
A separate temporary driver imported `PtxBinary32.Mixed` and invoked
`#print axioms` for each of the 44 explicit public definitions, types and theorem
declarations. The [complete audit](mixed-scalar-audit.txt) preserves every name
and report. All dependencies are limited to `propext`, `Classical.choice` and
`Quot.sound`; no custom axiom, `sorryAx`, `sorry`, `admit` or unsafe proof escape
was found. The public theorem dependency closure also covers the private
scalar-event helper used in the origin proof.

No independent proof or semantic blocker was found for this exact source.
The execution-to-memory-graph and numerical affine-kernel connections require
their own review; they are not established merely by this mixed-layer result.

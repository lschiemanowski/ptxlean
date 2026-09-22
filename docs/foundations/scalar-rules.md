# Reusable scalar verification rules

[`ScalarRules.lean`](../../Ptx/ScalarRules.lean) packages composition, preservation,
and termination arguments for the existing scalar instruction interpreter. The
rules do not change instruction semantics. Read the
[scalar machine guide](scalar-machine.md) first for its concrete arena, candidate
read, fault, and fuel conventions.

## Contracts distinguish stopping from finishing

An assertion is a predicate on the complete scalar state, including the program
counter. Four contracts express different promises:

| Contract | Promise |
| --- | --- |
| `Segment program fuel pre post` | Starting in `pre`, exactly this budget reaches `post` with status `exhausted`. |
| `Completed program fuel pre post` | This budget produces explicit `halted` status and `post`. |
| `PartialCorrect program pre post` | Every run that halts from `pre` satisfies `post`; termination is not asserted. |
| `TotalCorrect program pre post` | Every initial state satisfying `pre` has some finite budget producing `halted` status and `post`. |

The state-dependent budget in `TotalCorrect` is useful for loops with an input
length. The concrete interpreter is deterministic. These contracts do not
quantify over GPU schedules or assert that arbitrary weak-memory candidates are
valid executions.

`segment_comp` joins two exhausted segments. `segment_then_completed` joins an
exhausted prefix and a fixed-budget completed suffix. `segment_then_total`
permits a state-dependent suffix budget. All three use the proved `run_add`
equation, which preserves the full state, outcome, and concatenated trace.
Composition never restarts a halted or faulted prefix as if it had exhausted.

For example, a proof of a loop body can establish that its final PC is the loop
header and its counter has decreased. That fact belongs in its postcondition.
The next segment consumes precisely that state, not a fresh state whose PC or
registers were silently reset. These rules compose execution budgets for one
instruction list; they are not code-concatenation or branch-relocation theorems.

## Frame rule from actual store effects

`StoresTo event index` means that an executed occurrence emitted a store whose
byte address identifies the given word index. Predicate-false stores have no
memory effect. Loads do not count as stores. `TraceAvoids trace index` states
that no actual event in the trace stores to that index.

`runWith_frame` proves:

```text
TraceAvoids result.trace index
  → result.state.memory[index]? = initial.memory[index]?
```

Here `result` is the actual `runWith` result. The premise contains no final-memory
equality and does not substitute static register names for dynamic addresses.
The proof inspects instruction transitions: the only operation that changes
memory is a checked store, and list replacement preserves all other indices.
It then composes that fact along the execution.

The optional lookup notation makes the theorem meaningful even for an index
outside the arena: both sides remain absent. For an ordinary valid word, the
same equality preserves its exact 32-bit value. `step_frame` is the one-transition
rule, and `run_frame` specializes the whole-run rule to concrete reads.

Frame preservation holds for exhausted, faulted, unsupported, and halted runs.
A later fault does not undo earlier stores. It also holds with candidate load
values because every memory update still passes through the same store rule.
This does not establish those candidate values' memory-model admissibility.

The frame is local to the scalar state. It is not a separation-logic rule that
silently rules out writes by other threads. A shared-memory execution must apply
the one-step argument to every participating thread and establish the relevant
disjointness or interference conditions explicitly.

## Invariants and termination

`runWith_invariant` lifts preservation by each successful next-state transition
to every finite execution prefix. Fault and unsupported outcomes retain their
incoming state; exit also retains its incoming state. The rule therefore says
nothing by itself about successful completion.

`partial_of_invariant` takes an initial invariant, a next-step preservation proof,
and a proof that the exit case satisfies the postcondition. It proves partial
correctness without a termination assumption. An invariant may hold forever in
a loop; this theorem does not convert that into a completed execution.

`terminates_of_decreasing_measure` adds the missing progress argument. For every
invariant state, the next concrete dispatch must either:

1. halt explicitly with the postcondition; or
2. take a next-state transition preserving the invariant and strictly decreasing
   a natural-valued measure.

Strong induction on that measure constructs a finite budget and proves its
`halted` outcome. The rule does not assume the desired completed run. Its local
progress obligation excludes fault and unsupported outcomes, so a measure alone
is insufficient. For an instruction-level loop, a measure can combine remaining
iterations with position within the loop body; it must decrease at every actual
dispatch, including predicate-false instructions and branches.

These rules concern the interpreter's explicit arithmetic and arena discipline.
Their use in a kernel proof still requires justified input layouts, bounds,
precision/overflow specifications, and any concurrent memory-model connection.

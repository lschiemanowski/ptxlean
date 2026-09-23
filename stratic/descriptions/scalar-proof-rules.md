# Scalar verification rules

The rules let proofs for individual instructions and finite execution segments
be combined into proofs about a run. A segment is a sequence of steps within one
program. The contract states whether it proves a property of completed results,
safety of an initial part of a run, or termination. Composition retains the
program counter and stopping status; consuming the evaluator's step budget is
not treated as successful completion.

A frame argument proves that certain storage remains unchanged. It uses the
stores that actually occurred and the locations they can affect, rather than
assuming the desired final memory. Writes by other threads require a separate
interference argument. These rules support branching loops and kernel proofs
while distinguishing reads from concrete memory from proposed candidate values.

## Four different contracts

An assertion is a property of the full state, including the program counter.
A precondition (`pre`) must hold at entry; a postcondition (`post`) describes the
promised state afterward. All four contracts below quantify over every initial
state satisfying `pre`. They concern the concrete scalar interpreter, and `fuel`
is its maximum number of instruction dispatches.

| Contract | Guarantee |
| --- | --- |
| `Segment program fuel pre post` | Exactly that budget is consumed, status is exhausted, and the intermediate state satisfies `post`. |
| `Completed program fuel pre post` | That budget reaches an explicit exit with `post`; it need not consume the entire budget. |
| `PartialCorrect program pre post` | Every run that halts satisfies `post`; it need not halt. |
| `TotalCorrect program pre post` | Some finite budget reaches exit with `post`; the budget may depend on the initial state. |

Segment composition adds budgets and passes the actual intermediate state,
including its program counter, to the next segment. An exhausted segment can
also precede a completed or total-correct suffix. These rules apply to one
instruction list; they do not concatenate separately addressed programs or
relocate branch targets. Halted and faulted prefixes are never restarted as if
they were exhausted segments.

## Preservation and progress

The frame assumption says that no occurrence in the actual trace stores to the
word under consideration. Predicate-false stores emit no memory effect. From
that premise, the frame theorem derives equality of the initial and final word
lookups, including absence outside the arena. It holds for completed, exhausted,
and faulted runs, and also for candidate reads. It does not assume final-memory
equality or justify those candidates under the memory model. Other threads'
stores require a separate interference argument.

An invariant is a property that holds initially and is preserved by every successful transition.
Together with an exit case establishing the postcondition, it proves partial
correctness. Termination additionally requires that every invariant state either
executes exit with the postcondition or takes a successful step preserving the
invariant and strictly decreasing a measure, a nonnegative integer assigned to the state. This progress premise
excludes faults and unsupported outcomes. The measure decreases on each dispatch,
including branches and predicate-false instructions, not merely once per loop
iteration. Induction constructs a terminating budget instead of assuming a
completed run. None of these scalar rules supplies scheduler fairness, the assumption that
threads are not indefinitely denied opportunities to run.

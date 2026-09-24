# Adding a pure instruction family

`Ptx.Scalar.Pure32` supplies shared execution mechanics for operations that read
finite word/predicate inputs and write one 32-bit register. It imports only the
existing root scalar/environment modules. It introduces no new scalar machine,
memory operation, parser or admitted PTX form.

A `Family Operation` supplies the following:

| Field | Obligation |
|---|---|
| `wordArity`, `predicateArity` | Number of each kind of operand for each operation |
| `Results` | Permitted output words for an assignment of word and predicate values |
| `inhabited` | At least one permitted output for every assignment |
| `Supported` | Target and operation combinations admitted for fetched execution |

`Family.ofFunction` packages a total function as a single-result relation and
constructs its nonemptiness proof. It does not prove the function or target
predicate agrees with PTX. For nondeterministic specifications, supply the
relation directly. `eval_preserves_choices` proves the shared mechanism retains
distinct permitted outputs; `eval_deterministic` requires a separate uniqueness
proof. There is no implicit choice of one result.

An `Instr` has an outer guard, an operation, a destination and arity-indexed
operand functions. `Fin n` is an index smaller than n, so the typed instruction
contains exactly the family's operand counts. Word operands reuse `Operand32`.
`OperandPred.reg index positive` reads a predicate with the same polarity
convention as `Guard.pred`; false means negation. `OperandPred.imm` supplies a
Boolean constant. These generic forms do not imply legality in textual PTX.
A leaf decoder must reject unsupported forms and check register-type rules at
its stated frontend boundary. No generic instruction equality decision procedure
is assumed; leaf proof tests can use definitional equality or their own proved
finite decoding properties.

The outer guard decides whether the whole instruction runs. Predicate operands
are distinct operation inputs. When enabled, `Eval` applies the family's relation
to `Instr.wordValues` and `Instr.predicateValues` in the incoming state, then
writes the destination. `eval_alias_read` explicitly handles a word source naming
the destination. Repeated operands are allowed. A disabled instruction changes
only PC. `eval_positive_guard`, `eval_negative_guard` and their skip counterparts
cover both guard polarities. All predicate registers, address registers and
memory are preserved; all other word registers are preserved too.

The occurrence carries the actual family instruction. Metadata order is guard
reads, word operand reads in increasing argument index, then predicate operand
reads in increasing argument index. Repeated register reads remain repeated;
literals contribute none. `Instr.sourceReads_word` and
`Instr.sourceReads_predicate` show each register operand is included. A skipped
instruction records only its guard and no write. No occurrence has a memory
effect. These are syntactic operand lists, not a PTX memory-dependency analysis;
a selector may syntactically name inputs irrelevant to a particular result.
Do not use this coarse metadata as a no-thin-air admission rule.

`Step` requires actual fetch at the incoming PC and the family's target predicate
for that exact operation. Eligibility is checked even for a false guard. This
is fail-closed modeled admission, not a claim about hardware faults on invalid
instructions. `step_origin`, `step_iff_of_fetch`, `step_wrong_instruction` and
`step_wrong_pc` reject substituting an unrelated occurrence. `step_no_fetch`
excludes a missing instruction. `step_unsupported` excludes an inadmissible
operation; `step_false_iff` retains that condition even on a skipped instruction.
`eval_exists` uses the family's nonempty-result proof, while `step_exists`
additionally requires actual fetch and eligibility. Neither is a complete-kernel
termination or execution-fairness theorem.

## Evidence and source boundaries

Source SHA-256: `02eb8b1cb85b2d40f7e0befe65a75be57ae91cff09e6c2a78ad9c6e04ca98fd5`.

```
lake --no-cache build Ptx.Pure32
lake --no-cache env lean Ptx/Pure32.lean
```

The module build and fresh elaboration passed. All 46 explicit public
declarations, including 32 theorems, were independently enumerated and freshly
printed with `#print axioms`; the existing exact-name dependency auditor accepted
only standard Lean axioms. Full reports are in
[pure-instruction-families-audit.txt](pure-instruction-families-audit.txt).
The existing forbidden-token source scan passed.

Temporary development fixtures also kernel-checked a destination/source alias,
negative guard sharing a predicate with an operation operand, repeated ordered
reads, guard-only skipped metadata, rejection of an unsupported skipped
instruction, missing fetch, actual fetched execution, and two distinct admitted
results of a nondeterministic family. They were explicitly non-PTX mechanism
fixtures, not instruction acceptance evidence.

A future leaf must still prove its operation-specific mathematical statement,
its source/target conditions and its supported text boundary, and undergo source
review. Instantiating this structure changes no coverage ledger. Wider registers,
predicate destinations, memory, branches, exceptional outcome modeling, partial
result relations and full-program runners are outside this interface.

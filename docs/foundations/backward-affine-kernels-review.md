# Independent review of the four backward launches

Reviewed source: [`BackwardPipeline.lean`](../../integration/torchlean/PtxBinary32/BackwardPipeline.lean),
SHA256 `6173bf79baa3a8898c5245bb1122d24ad395a31fd39c2edde1723e840be8c582`. No source edits were made.
No semantic or proof blocker was found for the stated restricted contract.

## What is actually executed

The four requests all use the existing fetched seven-instruction `Affine.program`.
Their byte-offset argument lists select the documented initialized ten-word
arena: `[16,12,20,36]`, `[36,8,20,32]`, `[32,4,20,24]`, and `[32,0,20,28]`.
These give `q=2*d+0`, `db=q*A+0`, `dx=db*w+0`, and `dw=db*x+0` in that order.
The exact constant words are binary32 positive two and positive zero. Each
positive-zero addition remains a separate actual rounded instruction. The
`Results` relation retains all eight chosen multiplication/addition words.

`stage_run_iff` obtains its conclusion from `Affine.run_iff` and the proved
`stage_initial`, not a new assumed input/output semantics. Fixed small offsets
are aligned and within the ten-word prefix for every arbitrary tail. No
finiteness property is needed to establish valid addresses or complete runs.
`stage_trace_safe` identifies all seven actual events, their program counters
and their instructions, and derives every memory-access check from the actual
launch. This is not a trace invented independently of a fetched execution.

## Real writeback and shared intermediate values

`stage_launch_correct` connects the caller's live cell to the launch's actual
initial state through `run_from`; cell lookup uniqueness prevents selecting a
different input snapshot. Its final allocation comes from `writeback_lookup`
and `finish_words`, so the new words are consequences of the actual store.

`launches_correct` uses the resulting cell equality of each stage as the next
stage's input. The stored q from stage zero is therefore the q read by stage
one. Stage one stores db; both remaining stages read that same encoded db.
The intervening dx store changes only index six, leaving db at index eight.
No equality to an expected gradient or intermediate value appears as a premise.
The theorem retains the full final `State` and exact `Affine.trace` for every
stage. Thus the corresponding inherited address, predicate and untouched
register frames remain available, not merely a final numerical answer.

`pipeline_correct` applies this reasoning to every admitted completed four-stage
`Chain`. A chain contains actual halted runs and passes the exact resulting
`Store` between them; faulted execution or an advancing prefix does not count
as successful completion. Each launch receives its own arbitrary `Seed`, with
unconstrained initial registers and predicates. Those seeds are distinct from
the mathematical incoming sensitivity stored as `data.seed`; no arbitrary
register bank is silently carried between launches.

## Existence and preservation

`pipeline_of_results` is a constructor accepting eight permitted rounded results.
The separate `pipeline_exists` discharges that premise using `results_exists`,
whose underlying binary32 reference envelope is nonempty for all codewords.
Its only substantive initial conditions are the actual live, correctly owned
initialized cell and the existing numeric target eligibility condition.
It assumes neither finite data, a desired output, numerical accuracy nor a
successful stage. NaN/infinity inputs and arbitrary old output words therefore
remain covered by finite modeled execution existence, without any claim that
those answers are finite or numerically useful.

`pipeline_memory_frame` preserves the first six input/constant words and every
word of the arbitrary tail. `pipeline_other_allocation` preserves each other
logical allocation. The exact final `outputData` additionally identifies all
four replaced output slots. `stage_after_release_rejected` inherits permanent
non-revival of a released logical allocation through any valid later storage
history; it is stronger than checking only the immediately released state.

## Deliberate boundaries

The saved affine codeword A is an input of this four-stage API. It is not assumed
to be a correctly rounded forward value, nor proved to be one here. A separate
forward-prefix execution and numerical theorem must establish its provenance
and error. Likewise this layer does not prove approximation of the generated
TorchLean sensitivities; it supplies actual execution results to that later
bridge. The Stratic description and guide state those separations.

The program is manually selected, independently of TorchLean's automatic real
backward construction. The semantics remains the isolated one-thread global
word arena and serialized launch contract, with ISA 9.4 and numeric sm_70-or-later
eligibility. A real runtime still owes completion, visibility, valid argument
binding, lifetime continuity and absence of interfering accesses. Thread exit
alone does not establish those obligations. No general cross-kernel PTX memory
graph, GPU scheduling fairness or hardware realization of every NaN encoding
is inferred from these proofs.

This reviewer authored the underlying Affine module. This review is independent
of the BackwardPipeline author and checks its composition and specialization;
it is not a claim of independent authorship review of every imported library.

## Fresh checks

Fresh source elaboration passed with no diagnostics, and a separately generated
dependency driver audited exactly all 27 public declarations. The list was
independently matched against this source rather than assumed from a count.
Only `propext`, `Classical.choice` and `Quot.sound` occur. No `sorry`, new axiom
or `native_decide` appears in the reviewed source. The source hash remained
unchanged across the checks. Commands and full output are preserved in
[`backward-affine-kernels-audit.txt`](backward-affine-kernels-audit.txt).

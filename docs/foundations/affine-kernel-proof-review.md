# Independent review of the memory-backed affine kernel

Reviewed source: [PtxBinary32/Affine.lean](../../integration/torchlean/PtxBinary32/Affine.lean),
SHA-256 `62403b1b70e22e2ddcd14c0eac299fa2ab05f05e640a819cd963416880df32b5`.
The 43-declaration core was reviewed first. Two concrete fixtures and their
execution theorems were then appended; their final source, four new declarations
and the unchanged core were independently rechecked. The reviewer made no
proof-code changes. This review builds on the independent
[mixed execution review](mixed-scalar-proof-review.md) and the separately
reviewed binary32 instruction and numerical contracts.

## Initial conditions and actual execution

The concrete program contains three scalar loads, a binary32 multiplication,
a binary32 addition, one scalar store and explicit scalar exit. The register
banks are distinct: the store reads address register 3 and value register 4;
the multiplication's update of value register 3 cannot overwrite that address.
The five value registers are assigned before their values are consumed.

`Initial` requires only PC zero and validity of the four addresses held in address
registers zero through three. Validity supplies alignment and bounds in the
initial word arena. There are no address inequalities, assumptions about initial
value-register contents, finite-input restrictions or desired output facts.
All input/input and input/output aliases are included. The `input` helper's
optional/default lookup is always in range under these conditions; `input_get`
proves equality with the bounded list lookup used in the graph witness.

`run_iff` characterizes every terminal `Mixed.Run` from this initial state. It
retains arbitrary admitted multiplication and addition choices and derives the
same actual intermediate word as the addition's source. Its reverse direction
constructs the actual seven dispatches for each allowed pair of arithmetic
results. The exact final state, halted status and complete event trace are
conclusions, not assumptions attached to a generic execution relation.

All three loads occur before the only store, and their values refer to the
initial memory snapshot. `finish` changes only the output word in that snapshot.
`finish_output` uses initial address validity to establish the actual stored-word
lookup. `finish_other_memory` excludes only the queried output location, so an
input aliasing the output is correctly allowed to change. Address registers,
predicates and value registers outside zero through four are preserved.

## Existence, finite paths and faults

`run_exists` constructs a halted run from any eligible initial state, including
arbitrary exceptional binary32 inputs. It uses numerical existence twice; it
does not restrict the universal evaluator to those chosen reference results.
`run_completed` derives halt, PC six and exactly seven events for every terminal
run. Therefore a fault or unsupported terminal run cannot arise from the stated
initial conditions.

`advance_pc` derives one-position advancement and excludes advancement from the
exit position. `path_control` and `path_bound` apply to arbitrary admitted finite
advancing paths, independently of FP result choices, and bound them by six steps
from PC zero. These paths remain prefixes, not implicit completed runs. Together
with the explicit terminal characterization and witness, this avoids relying on
fuel exhaustion or one favorable run as the control argument. It does not claim
hardware scheduling or progress.

## Concrete execution checks

The final module adds two named examples using `run_iff` in its constructive
direction. `disjoint_example` starts with the encodings of 1.5, 2.0 and 0.25,
nonzero incoming working registers, and separate valid input/output addresses.
It proves an actual seven-dispatch run and the exact final memory with 3.25 in
the output slot. `all_alias_example` uses a one-word arena initially containing
1.0 with all four addresses zero; it proves the actual run and the final 2.0
word for 1.0*1.0+1.0. Both discharge address conditions and fixed arithmetic
results, without assuming the desired execution. Their fixed result bits require
kernel reduction when applying `envelope_self`.

These fixtures complement the arbitrary-state theorems; they do not establish
new architecture coverage or weaken the unrestricted alias contract.

## Actual memory effects and source grounding

`trace_memory` exposes all four memory effects of the complete seven-event
trace. `memoryProjection` retains each event's actual PC, address and word value;
it interprets the selected global accesses as relaxed GPU/generic whole-word
operations. `trace_memory_witness` proves equality of the entire filtered
projection with all four program-event labels of the `AffineMemory` witness.
The original positions zero, one, two and five are preserved, not replaced by
the indices of the compressed memory-only list.

The witness contains initialization separately, once per initial arena location.
Its program labels use the initial load values and arbitrary actual output word.
`run_memory_witness` derives both the actual final stored value and the projected
trace equality from an arbitrary run, then supplies the proved `Graph.Valid`
witness. It does not assume memory validity or substitute an unrelated event
table for the run. Checked byte-to-word conversion uses the same valid addresses
as the actual accesses. No distinct-address premise is introduced by this bridge.

The reviewer authored the generic `Ptx/AffineMemory.lean` component; review of that
component itself is assigned separately to the coordinator. This independent
review concerns its use by the separately authored affine execution and trace
bridge, not a claim of independent authorship review for the generic component.

`RegisterDependency` is defined from actual trace events' read/write metadata.
It has no writer-before-reader condition built into the definition.
`register_dependency_forward` proves that order for every edge of this concrete
program, and `register_dependency_acyclic` derives acyclicity. `run_grounded`
combines that fact with the actual run's arithmetic result relations, exact trace
and valid memory witness. The arithmetic clauses connect initial loaded values,
actual intermediate and actual output; metadata alone would not prove that value
connection. These results do not state that `Graph.Valid` is sufficient for
arbitrary dependent PTX programs or implement a general no-thin-air semantics.

## Error on the stored word

`stored_error` first inverts the actual run. It then invokes the existing
`Error.affine_results` for the actual intermediate and output, and connects its
conclusion to `final.memory[outputIndex s]?`. It covers every admitted completed
run, rather than a numerical reference chosen for existence.

The numerical premises identify finite initial encoded values `xh`, `yh`, `bh`,
bound their deviations from ideal inputs, and require exactly these input-only
range guards:

```text
|xh*yh| ≤ maxFinite
|xh*yh| + eps32(xh*yh) + |bh| ≤ maxFinite
```

There is no assumed finite intermediate, correct output or finite final result.
The deviation inequalities imply nonnegative error budgets when satisfiable;
there is no need to add separate positivity premises. The inherited budget
contains both rounding contributions, the two multiplicand perturbations,
their product term and the bias deviation. It concerns two separately rounded
operations, not a fused multiply-add. Bit equality and real-value error remain
separate conclusions.

## Source scope and checks

The selected PTX slice uses `.b32`-compatible value registers, bit-preserving
`.u32` global memory transfers, explicit relaxed GPU scope and `.rn.f32`
arithmetic. ISA94/sm70 eligibility includes the necessary scoped memory and
subnormal-support feature conditions. These source interpretations rely on the
[pinned PTX 9.4 manual](../../references/nvidia/ptx-isa-9.4/index.html), especially
[operand type compatibility](../../references/nvidia/ptx-isa-9.4/index.html#operand-type-information),
[loads](../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld),
[stores](../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st),
[multiplication](../../references/nvidia/ptx-isa-9.4/index.html#floating-point-instructions-mul)
and [addition](../../references/nvidia/ptx-isa-9.4/index.html#floating-point-instructions-add).
The model's isolation, uniform whole-word access, resolved arena offsets and
register-declaration boundaries remain explicit. No raw PTX parsing, runtime
permission proof, hardware conformance or exact NaN realizability is established.

Independent checks, run from `integration/torchlean`:

```text
lake env lean PtxBinary32/Affine.lean
lake env lean /tmp/affine-independent-audit.lean
```

Both exited successfully. Fresh elaboration produced only an unused-simplifier
argument warning at line 233. The temporary audit driver imported the module and
printed dependencies for all 47 explicit public definitions and theorems. An
independently enumerated list exactly matched the author's endpoint list.
The [complete audit](affine-kernel-audit.txt) retains all 47 names and reports;
only `propext`, `Classical.choice` and `Quot.sound` occur. No proof hole, unchecked
custom axiom or unsafe proof escape was found. Public proof dependency closure
includes the private instruction and lookup helpers used by those proofs.

No independent semantic or proof blocker was found for this exact affine source.

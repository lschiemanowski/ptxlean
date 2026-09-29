# From the middle phases to the stored cell result

The middle phases leave two small matrices, S5 and S6, in shared storage.
The last phase calculates `S5 D + S6 B`. Each active lane calculates one
coordinate, using two ordered dot products, a final rounded addition, and one
eight-byte global store. This completes the arithmetic of a local Poisson cell.
It does not yet complete the proof of a whole concurrent cell launch.

## The final instruction proof

[CellFinalKernel.fetched_correct](../../integration/torchlean/PoissonPTX/CellFinalKernel.lean)
follows the actual program counter through both contractions, the addition,
the integer output-index calculation, address instructions, store and return.
Every completed run writes the calculated logical binary64 value. Shared memory
and global bytes outside the output word remain unchanged.
`fetched_exists` independently constructs a completed run for every valid input
snapshot. This is execution existence in the formal model, not GPU progress.

The conditions are concrete: the thread starts at the final body's first
instruction, its input operands occupy valid aligned eight-byte locations,
and its actual output address is valid. The input values are arbitrary.
The proof preserves the separate rounded multiplication and addition and their
increasing inner-index order. It does not replace them by real-number algebra
or fused multiply-add. NaN encoding freedom is retained through decoded equality.

[CellFinalLayout](../../integration/torchlean/PoissonPTX/CellFinalLayout.lean)
supplies the per-load conditions from allocated operand matrices for widths two
through five. It also relates the actual modular integer instructions to the
ordinary output address:

```
index   = cell * width * width + lane
address = globalBase + outputOffset + 8 * index
```

The first expression must fit in 32 bits, and the byte address must fit in
64 bits, be aligned and lie in the output allocation. Outside these conditions,
the instructions still have their modular semantics. For coordinate `(i,j)`,
the lane must be `i*width+j`; the local body proof takes these entry registers
as supplied and does not prove their initialization by the prologue.

## Composing with the middle phases

[CellFinalSnapshot.completed_from_middle](../../integration/torchlean/PoissonPTX/CellFinalSnapshot.lean)
uses an actual completed concurrent middle run and its necessary byte-source
constraints. The earlier proof identifies the actual stores of all six
intermediate matrices. The new proof builds shared bytes from these stores and
proves that loading an aligned word recovers exactly its recorded bits.

The final fetched run starts from that constructed storage, the initial global
coefficient bytes, and explicit entry registers and allocation bounds. Its
stored value is the corresponding coordinate of TorchLean's complete
`localAction` on the initial basis B, derivative D, weights W and shared input U:

```
Bᵀ (W ⊙ ((B U) Dᵀ)) D + Dᵀ (W ⊙ ((D U) Bᵀ)) B
```

Here `⊙` multiplies entries individually, and `ᵀ` swaps rows and columns.
Parentheses fix the operation order. Every matrix product uses TorchLean's
ordered binary64 fold. No hypothesis supplies the desired intermediate answer. The companion
`exists_from_middle` theorem also constructs a completed final run with that
result, provided its concrete input and output storage is valid.

The distinction still matters: constructing a snapshot from stores does not
prove that later loads in **one concurrent execution** observe that snapshot.
The next full-cell obligation is to extend the executed store/barrier/read-source
argument through these final loads. It must also connect the entry registers and
initial shared input to the actual prologue and gather. Complete PTX memory
admission, assembly, reductions, PCG kernels, host composition and hardware
conformance retain their separate boundaries.

## Checking it

From the repository root:

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_poisson_contractions.py'
```

`CellFinalChecks` uses asymmetric nonzero matrices and a nonzero cell/lane index.
It kernel-checks the completed stored result, rejects subtraction in place of
the final addition, and checks short and unaligned output storage and modular
index overflow. These are regression checks alongside general proofs.

The saved-run checker compares the complete final body and return in each of the
three element entries with the same Lean program consumed by the proofs:

```sh
python3 hardware/check_poisson_contractions.py \
  --run .hardware-runs/poisson-certified \
  --output /tmp/poisson-contractions-check.json
```

Use a fresh output path. Saved hardware artifacts are local empirical evidence;
they are not required for the Lean proofs. Exact text binding and mutation tests
check the program connection, not NVIDIA hardware conformance. This proof work
does not add a new GPU run.

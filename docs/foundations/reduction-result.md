# Following the actual reduction accumulator

The arithmetic proof follows every instruction boundary of the leader's loop.
Before an iteration, the counter records how many input words remain and the
accumulator is the modular sum of the preceding prefix. After the load, register2
contains the next input. After the add, the accumulator includes that word;
after the counter decrement, the shorter remaining count describes the same
extended prefix. The pointer can temporarily be one slot ahead of the counter
between the address increment and the decrement. This temporary difference is
recorded explicitly rather than treating the whole iteration as one instruction.

`SharedReductionLoop` proves the counter and pointer facts from actual fetched
moves, branches and updates. `SharedReductionResult` derives its smaller `Shape`
interface from that invariant. The arithmetic result therefore does not assume
initial loop registers or a supplied final sum. Arbitrary initial register banks,
finite interleavings and candidate read choices remain quantified.

The named `ReadContract` says only that an actual emitted shared load at input
index `i` returns that input word. This intermediate contract is discharged by
the combined candidate graph's publication/source theorem. It is not an extra
runtime promise in the final memory-valid execution result. The local
`observed_value` theorem connects the contract to the exact observation selected
by the actual successful load step. `total_succ` then relates the next prefix to
the real modular addition executed by the following instruction.

`global_store_sum` covers every output memory effect in an arbitrary candidate
trace. The result concerns the word actually read from the accumulator by the
fetched global store. A finite prefix can stop before producing such a store;
existence of a complete run is proved separately. Memory-validity assumptions
must be supplied by the combined memory model, not replaced with desired read
values or a host-side copy of the expected result.

`SharedReductionWriteback` records the persistent-memory consequence. Global
memory is initially unchanged. Once the actual output store succeeds, it is
exactly `input.set n (total input n)`; every other input and extra tail word is
preserved. Reaching output PC1 records successful completion of that store.
The independent terminal-position invariant proves that a halted leader must
have reached this position. `Writeback.halted_leader` therefore needs no assumed
output event, successful store or final memory equation. Its read contract is
the same one discharged by the combined memory model.

Both arithmetic and writeback modules pass the normal pinned Lake build. All
23 public declarations were enumerated and audited with `#print axioms`; the
exact source hashes and reports are in `reduction-result-audit.txt`. Only the
standard Lean logical axioms occur.

# Independent emitted-access safety review

Reviewed `Ptx/SharedReductionSafety.lean`, SHA256
`ebc9453ae63a4b200f3ae36df864620fa718970223c3d27f0bc8a175561eb8b4`.
No correctness blocker found. Fresh source elaboration was warning-free. All
seven explicit public declarations were independently enumerated and dependency
audited; only standard Lean axioms occur. The local forbidden-token scan passed.

The selected persistent arena is global or shared according to the emitted space,
not the lane scalar evaluator's temporary memory view. The scalar wrapper installs
that actual arena before evaluation. The proof inverts the actual successful
evaluation and emitted memory effect, then applies Scalar.eval_memory_safe.
Scalar halted events have no memory effect; faults and unsupported operations
emit none. Branches, exits and barrier events cannot forge scalar accesses.

Length preservation covers every scalarStep outcome, every fetched instruction
and every finite run, for arbitrary supplied read choices. Stores update an
existing word and cannot resize either arena. The run proof transports later
valid-address facts back to the original selected arena using these exact length
equalities. Thus the conclusion includes both four-byte alignment and an
in-bounds word index for every actual emitted memory effect.

This is emitted-access safety, not a theorem that arbitrary starts, schedules or
candidate read choices never fault or always terminate. It does not establish
ownership, permissions, hardware memory behavior, source/coherence validity or
the reduction output. Those separate obligations are not hidden as safety
premises. No graph validity or desired value is assumed here.

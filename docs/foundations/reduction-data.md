# Where a producer's address and value come from

A candidate schedule may stop early, interleave threads arbitrarily, or propose
arbitrary values for its loads. These freedoms do not let it invent a producer's
address or silently replace the value being published.

`SharedReductionData` follows register0 and address register0 through the actual
conversion and two doubling instructions. Its invariant continues through the
publication and barrier blocks. An actual global input load or shared store
therefore uses byte offset four times the issuing thread's lane number.
`runWith_producer_address` proves this for any finite candidate schedule. It does
not depend on a good memory source, a selected schedule or a correct final sum.

`SharedReductionValues` records actual global-load events. The producer's value
register must match a recorded load once that instruction has executed; branches,
waiting and barrier release preserve this fact. The theorem `shared_store_path`
returns a two-event subsequence of the actual trace: an earlier global load and
the shared store, both carrying precisely the stored word. The load belongs to
the same thread, and its address is independently fixed by the address theorem.
Thus value provenance comes from execution, while the combined memory constraints
must separately establish that the load observed the initialized global word.

These proofs cover arbitrary supplied register banks, candidate observations and
finite schedules. They do not assert that a schedule completes, prove memory
visibility or establish the leader's sum. The whole-program existence theorem,
barrier history, memory graph and accumulation argument provide those distinct
obligations. The dispatcher remains target-neutral; qualifying the selected PTX
forms, a valid physical launch and correspondence of logical storage to actual
allocations remain explicit at their respective boundaries.

Both modules freshly build. All 24 public definitions and proof endpoints were
independently enumerated and inspected with `#print axioms`; the dependency
report is `reduction-data-audit.txt`. Only Lean's standard logical axioms occur.

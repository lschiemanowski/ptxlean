# Worker-derived computation pilot

This two-family exploratory pilot selects `bfi.b32` and plain `lop3.b32` against
the pinned PTX 9.4 manual. Definitions of the common execution adapters and exact
universal theorem statements are supplied. Unlike batch-v1, no computation body
is supplied: Luna must implement it and prove the source-derived output-bit law.
That law still specifies every output bit. This tests implementation freedom
under a precise specification, not unsupervised interpretation of the manual.

Before dispatch, the coordinator checks the complete acceptance driver and a
separate concrete-case driver on reference fixtures. For each family, a deliberate
semantic fault must compile with its own proofs, pass a dependency audit and fail
a concrete assertion. The reference implementations are local preparation,
excluded from the worker base and task inputs. Their hashes, checks and final
sources are retained as coordinator evidence after generation. Draft preflight
repairs are not worker repairs. The contract and drivers are frozen in a commit
before worker invocation; any later corrections must be reported explicitly.

Luna runs through the existing recorded Codex headless campaign. Existing shared
semantics are immutable and there is one allowed output module per task. Every
attempt, feedback round and interruption is retained; the existing 200-call
campaign check-in remains in force. Fresh replay rebuilds from the frozen base,
runs the independent drivers and audits all public definitions and proofs. The
coordinator separately inspects source fidelity and theorem hypotheses.

The independent advisory reviewer remains `z-ai/glm-5.3-flash` through OpenRouter,
using the existing v4 prompt and schema, temperature zero, medium reasoning and
16,384 output tokens. The runner now adds a 600-second total request deadline to
its 300-second socket timeout. No automatic retry or fallback is permitted.
A deadline receipt records an infrastructure failure, not a semantic verdict;
provider work and billing may continue and remain unknown without a receipt.
Any manual retry is a distinct recorded request with unchanged packet bytes.

Before review calls, freeze four fixture packets: one control and one compiling
fault per family, without exposing their labels to the reviewer. Also review each
actual candidate separately. Score concrete seeded-fault findings and false alarms
separately; adjudicate claimed executable counterexamples with Lean. Keep all
vendor-bearing packets and raw responses local. Public reports contain hashes,
project-authored adjudications and numeric outcomes, not raw model prose.

Record worker durations and calls, feedback and checker repairs, request outcomes,
reported token usage and costs, and missing billing. Record coordinator phase wall
intervals starting with source/infrastructure preparation; these include tool waits
and are not measurements of active attention. Report the produced preparation
artifacts and repairs explicitly. Batch-v1 did not measure coordinator attention,
so this pilot cannot establish a quantitative preparation-time improvement.

Completion means source- and proof-reviewed integration of both selected forms,
or an exact remaining obligation for any rejected or unresolved family. Do not
weaken the contract to obtain acceptance. Keep other widths, predicate-producing
variants, complete ISA coverage and hardware conformance outside the result.

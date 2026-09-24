# Assisted LOP3 continuation

This continues the failed `lop3-v1` pilot using shared proof support, with a new
frozen repository base and a fresh headless Luna session. It is not a held-out
or independent replication. All earlier attempts remain in the original report.
The original contract and both acceptance drivers remain byte-for-byte unchanged.
Only `Ptx/Lop3.lean` may change in the worker checkout.

Start from the exact prior worker patch
`formalization/review/candidates/lop3-003.patch` (apply it in your checkout).
Read `formalization/contracts/lop3-v1.md` for the full obligations and source
anchors. Read `Ptx/BitVecProof.lean`, `examples/bitvector_proofs.lean`, and
`docs/formalization/bitvector-proofs.md` for the new support. You may import that
module and use its proofs. Finish the instruction's bit law and both exact decoder
directions; keep every input, target, guard, event and operand condition unchanged.
You may retain or change your prior computation, but report any change and why.

The prior private observe_if statement lacked parentheses around its Boolean
right-hand side and therefore did not express the intended equality. The shared
getLsbD_ite_zero has the correct explicit statement. Width conversion helpers
expose the range conditions needed by the two decoder directions. These helper
proofs and worked examples are coordinator assistance, not worker discoveries.
They do not contain a LOP3 computation or its full instruction-specific proofs.

Run both unchanged drivers, not just the module build. Audit public definitions
and proofs. No proof placeholders, new axioms, native_decide, contract/checker
changes, commits or extra model calls. No inspection of coordinator reference
fixtures in archived trial evidence; use the listed inputs and existing accepted
leaf modules. Historical fixture archives remain in the repository, so this is
an instructed input boundary, not a claim of isolation from reference solutions.
Report remaining obligations honestly if any cannot be completed.

Acceptance still requires a fresh clean replay with all original properties,
complete dependency audit, coordinator source/statement review, and a separately
recorded advisory source review through the existing OpenRouter route. An absent
model verdict is reported as unavailable, never converted to acceptance. The
coordinator's source review and Lean checking remain independent requirements.
No automatic review retry, fallback, or weaker specification is authorized here.

Record all worker calls and repairs, exact base/patch/helper hashes, preparation
and checking, review requests and unknown billing. Keep original failures intact.
One success after assistance would demonstrate recovery on this task; it would
not establish that the toolkit generalizes or that coordinator effort decreased.

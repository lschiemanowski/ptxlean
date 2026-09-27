# Bounded exponential instruction trial

The accepted leaf models `ex2.approx.f32` for finite nonpositive inputs,
infinities and NaNs, with exact special cases and the declared union of two
ULP interpretations. Positive finite operands are legal PTX but unsupported by
this fragment. A false predicate skips any operand. This is a restricted model,
not accepted full-form ISA coverage or a complete softmax kernel.

Two headless calls requested GPT-6 Luna (campaign calls 33 and 34); the second
was a repair. Provider-confirmed model identity is unavailable. The coordinator
supplied the numerical provider and exact contract. Before generation, the full
frozen driver passed a separate coordinator reference fixture and rejected four
compiling, axiom-audited mutants: ignored operand, FTZ spelling, wrong fetch and
weakened SM floor. The fixture was excluded from worker inputs. Draft checker
repairs preceded dispatch and are preserved separately from final calibration.
This is evidence for bounded integration work, not independent semantic discovery
or a general productivity estimate.

The first worker candidate had an incomplete decoder proof. The repair changed
only that proof body; no definitions, theorem statements or acceptance checks
changed. The final candidate is integrated byte-for-byte. Independent semantic
and proof reviews passed with the documented partial-domain and ULP qualifications.
Fresh pinned replay passed the frozen driver and audited all 24 public declarations,
with only `propext`, `Classical.choice` and `Quot.sound` dependencies.

The first replay failed after `/tmp` exhausted file entries during dependency
setup; final status persistence failed too. Logs and a separate recovery note
preserve that outcome. Only generated caches owned by this task were removed,
and a new independent replay on the main filesystem passed. Neither the failed
replay nor the first incomplete worker candidate is acceptance evidence.

`worker-evidence.tar.gz` preserves both worker attempts, replay logs, the recovery
and cleanup records, reference calibration, earlier checker diagnostics and
frozen coordinator inputs. `evidence-manifest.json` hashes each member. Raw model
transcripts are omitted because they can contain vendor source excerpts; their
sizes and hashes, and the original private archive hash, preserve that boundary.
The vendor manual and dependency worktrees are not distributed.

Run `bash scripts/check.sh` from the repository root and
`python3 integration/torchlean/check.py` for the pinned floating integration.
The latter includes the frozen exponential acceptance driver and exact dependency
audit. See the [source review](../../../docs/formalization/exponential-instruction-source-review.md)
for semantic qualifications and the [study guide](../../../docs/foundations/stable-softmax.md)
for the surrounding numerical argument.

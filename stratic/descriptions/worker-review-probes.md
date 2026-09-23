# Worker review probes

Independent acceptance checks should reject a definition that proves its own
claims but gives the wrong instruction meaning. Offline probes deliberately
introduce a known defect into a recorded candidate, compile its definitions and
own proofs, and then run the coordinator's independent checks. A defect counts
as detected only when the candidate still builds and the independent check fails
at the expected distinguishing assertion. A build failure, unrelated diagnostic,
missing dependency or interrupted process is inconclusive, not semantic detection.

The min/max probes cover two specific defects. One removes a supported instruction
name from the malformed-input classification while retaining its successful
decoder. The other exchanges the minimum and maximum textual meanings while
changing the encoder and the worker's own examples consistently. Their successful
compilation shows why internal proof consistency and round trips alone cannot
establish agreement with PTX. An unchanged positive control must pass both stages.

Register-read probes cover information that arithmetic-only proofs can miss.
Removing a bit-count source read, or both binary32 operand reads, leaves the
state computation and the candidate's own proofs intact. Independent expected
event records must still reject the missing reads. Repeated reads of the same
register remain repeated in the record; a predicate read is separate from the
operand reads. An unchanged candidate must pass, and the mutant must both compile
and pass dependency inspection before the exact intended trace assertion fails.

Each probe uses the recorded candidate's pinned base and saved patch in an
isolated checkout or source overlay over a completed fresh replay. An overlay
places rebuilt candidate modules ahead of the unchanged replay dependencies.
The probe preserves exact input hashes, mutation diffs, commands, exit statuses
and diagnostic locations. It makes no model calls and leaves the candidate and
main checkout unchanged. Stored inputs allow repetition without regeneration.

Detecting these seeded defects is evidence about these checks and these
errors. It is not a general reviewer-quality score, an unbiased sample of model
mistakes, or proof that every semantic error will be detected. Further families
need their own independently prepared obligations and distinguishing cases.

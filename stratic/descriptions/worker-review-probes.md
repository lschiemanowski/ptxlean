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

Each probe starts from the recorded candidate's pinned base and saved patch in
an isolated checkout. It preserves exact input hashes, mutation diffs, commands,
exit statuses and diagnostic locations. It makes no model calls and leaves the
candidate and main checkout unchanged. The replay command uses the stored patch
and independent driver, so evaluation can be repeated without regeneration.

Detecting these two seeded defects is evidence about these checks and these
errors. It is not a general reviewer-quality score, an unbiased sample of model
mistakes, or proof that every semantic error will be detected. Further families
need their own independently prepared obligations and distinguishing cases.

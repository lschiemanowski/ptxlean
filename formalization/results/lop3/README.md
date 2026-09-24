# Three-input logic worker evidence

**Not accepted or integrated.** Three Luna calls with two rounds of proof guidance
left the conditional bit-observation helper, universal `compute_bit` property and
both typed-decoder directions unfinished. The final fresh replay fails compilation;
it never reaches the acceptance drivers or dependency audit. The precise remaining
obligation is in [outcome.json](outcome.json).

See [the pilot report](../derived-v1/README.md) for evidence and restrictions.
To reproduce the failure, extract `worker-evidence.tar.gz`, create a detached
worktree at the `base_commit` in `outcome.json`, apply
`attempts/lop3-003/candidate.patch` there, and run `lake build Ptx.Lop3`.
The archive includes the failed fresh replay's `modules.log`. Do not apply this
candidate to the accepted main-project build.

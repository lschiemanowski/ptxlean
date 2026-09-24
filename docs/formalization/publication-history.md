# Publication history and retained evidence

Before the first source release, the unpublished Git history was cleaned to remove
NVIDIA's PTX manual and raw worker event transcripts, including copies in evidence
archives. The already public initial commit was preserved. The
[commit map](../../references/publication-history.json) lists the original and
cleaned revisions and the paths changed in each tree. Commits preceding the first
bundled manual are unchanged. No Lean source file changed in this operation.

For each historical archive, only raw `events.jsonl` members were omitted. Every
retained member is byte-identical to the original. Its manifest records the
original archive digest and the omitted members' names, sizes and digests; its
current hashes describe the distributed subset. The accepted-form ledger's
manifest hashes were refreshed accordingly. The final cleaned tree is identical
to the reviewed source-acquisition cleanup before the history rewrite.

Original task files, receipts, acceptance records and Stratic review records keep
their original commit and tree identities. The commit map documents a content
transformation; it does not make old reviews attest to different trees or imply
that original runs used the cleaned commits. Some historical task bases were
private worktree commits rather than ancestors of `main`; the map makes no claim
to include those separate histories.

A public checkout can verify the distributed archive hashes and accepted-form
provenance, build the current Lean proofs, and record new worker runs using its
own commits and the locally acquired, hash-pinned manual. It cannot exactly replay
historical tasks whose original Git bases are absent. The runner deliberately
rejects a missing base instead of substituting a mapped revision. Exact replay
requires the original private history and all pinned inputs; resuming an original
model session additionally needs its local session records. Historical check logs
are retained evidence, not a promise that all original environments are publicly
reconstructible.

For publication, check the branch that will actually be sent:

```sh
python3 scripts/check_distribution.py --history main
```

This scans every reachable commit's files and archive members for known manual
artifacts and raw event transcripts, including files deleted later. It does not
certify the absence of every copied quotation. Check each intended release branch
or tag separately. Publish only the checked refs; do not use a mirror push or
publish private recovery files.

The original local `main` history is retained in an ignored private recovery bundle under
`.formalization-runs/private-history-before-publication/`; original evidence
archives are retained separately under
`.formalization-runs/private-evidence-before-publication/`. These files and local
source caches are not part of the release tree or its reachable history. A fresh
clone of the cleaned `main` was used to check that original manual objects are not
transferred with that branch.

# Independent model review

A semantic reviewer compares a candidate instruction definition with the pinned
PTX source and the task's explicit restrictions. It is a separate invocation
from generation. It can identify a mismatch, find a concrete counterexample, or
report an unresolved question; agreeing with a candidate is not proof that its
meaning is correct. Lean checking and coordinator acceptance remain separate.

A review packet fixes a repository commit, candidate file hashes, supporting
interfaces, source section hashes, and project-authored obligations. The vendor
source is read only from the verified local manual. The same packet can be sent
to different reviewers. Evaluation labels, mutation descriptions, original
acceptance verdicts and generating-model conversations are excluded from the
request. Candidate text is review material, not instructions to the reviewer.
The first implementation reviews a supplied context without tools; it records
this limitation instead of claiming the reviewer inspected the whole repository.

OpenRouter requests select one exact model identifier and require supported
request parameters. Each invocation is reserved in a durable record before the
request, and retains its requested and returned model identity, provider when
reported, exact request and response hashes, timing, token usage and reported
cost. Missing usage or cost remains unknown. A failed request, truncated answer,
invalid report or interrupted invocation is not a semantic verdict. There is no
automatic retry or model substitution. Retrying is a new recorded invocation.
Credentials are read at execution time and never written into records.

Reports identify the obligations considered, findings tied to candidate locations
and source anchors, and remaining uncertainty. References and report structure
are checked mechanically. Such validation does not establish that a finding is
true. The coordinator adjudicates findings before using them for acceptance.

Evaluation uses both unchanged candidates and deliberately altered definitions
that still compile with their own proofs. Independent checks confirm the planted
fault. A reviewer receives neither the expected verdict nor the mutation label.
Detection requires a finding that explains the planted semantic mismatch; a
bare rejection, unrelated criticism, or infrastructure failure does not count.
The review protocol and case packets are fixed before a fresh evaluation.
Cases used for subsequent tuning become development evidence, and related
variants are reported together rather than counted as independent instruction
families. Correct fixtures and faulty fixtures must first compile with their own
proofs; the distinguishing assertion must fail because of its meaning.
False alarms on unchanged candidates and additional genuine defects are recorded
separately. Small adaptive trials describe those cases, not a general accuracy
estimate or justification for automatic integration.

Requests and raw responses can reproduce vendor passages and remain in ignored
local records. Public artifacts contain recipes, source locators and hashes,
project-authored adjudications and numeric results. Publishing model prose needs
separate inspection; a raw response is never automatically exported.

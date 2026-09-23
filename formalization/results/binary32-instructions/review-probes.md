# Binary32 instruction metadata probe

The unchanged final candidate passed the independent driver. A copy with both
operand-register reads removed from executed instruction events still compiled
all its definitions, proofs and examples, and all 28 public dependency reports
used only standard Lean axioms. The same driver rejected that copy at exactly
line 50: the expected event reads predicate 5 and word register 3 twice, while
the mutant omits both word reads. Arithmetic and register updates were unchanged.

The [result record](review-probe-result.json) pins the candidate, driver, replay,
harness and command outcomes. The evidence archive preserves the source overlays,
mutation diff, exact harness and diagnostics under `review-probes-v1/`. Compiled
artifacts are excluded. Dependencies were reused from the coordinator's completed
fresh replay, never from a worker cache. Neither the accepted candidate nor its
replay checkout was edited. No model call was made.

The first control attempt failed because Lean resolved the numerical parent
module in the incomplete overlay. It established no semantic detection. After
copying the reviewed parent build artifacts into each overlay, both controls
and the mutation behaved as intended. The final run also tightened the check to
require exactly the intended assertion, diagnostic kind and expected read list.
Both earlier harnesses and their outputs are preserved as setup history.

This shows detection of one chosen metadata defect. It does not measure a
general semantic-error detection rate or prove that the review process is complete.

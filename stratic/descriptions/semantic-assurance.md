# Semantic fidelity

Each semantic interpretation connects a versioned source passage and its
qualifications to a plain-language explanation, formal rules, and examples of
permitted and forbidden behavior. Ambiguities and interpretive choices remain
visible. The source and evidence records allow the interpretation to be reviewed
and reproduced independently of its author.

Document review addresses fidelity to NVIDIA's promises, exceptions, undefined
behavior, version requirements, and target restrictions. Internal adequacy
results establish that semantic components fit together, suitable programs
admit executions, and derived rules follow from the foundation. External
examples, litmus tests, and hardware experiments provide evidence for detecting
errors without being presented as general proofs of hardware conformance.

Model-assisted formalization uses inexpensive models for generating definitions
and proof candidates. Lean checks submitted proofs, while source review and
independent checks address whether their definitions describe the intended
behavior. Generation records identify the inputs, outputs, checking results,
and costs needed to assess reproducibility and cost effectiveness. A generator
agreeing with its own definitions does not establish semantic fidelity.

The explanation of a rule states which parts of its justification come from
source interpretation, checked theorems, assumptions, or experiments. These
explanations also provide material for studying the computing model.

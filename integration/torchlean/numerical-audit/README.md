# Pinned numerical prerequisite checks

These checks verify existing FloatLib/TorchLean APIs. They add no PTX numerical
semantics and do not choose a network precision policy.

From `integration/torchlean`:

```sh
lake build NN.Floats.IEEEExec.Bridge.Finite
lake build NN.Floats.FP32.Error
lake env lean numerical-audit/finite-audit.lean
lake env lean numerical-audit/format-error-audit.lean
```

Both builds and both fresh elaborations passed. The drivers report 26 distinct
existing theorem endpoints, all with only `propext`, `Classical.choice` and
`Quot.sound`. They also instantiate lossless encoding and arithmetic-refinement
contracts at the concrete `ExecFloat.Binary 8 23` type. `receipt.json` records
pins, commands and hashes; `import-closure.json` records source hashes for all
4,111 actually imported modules. The broad dependency closure is the effect of
the selected upstream umbrella imports, not a recommendation to make the root
PTX library depend on all of them. These probes import no `Ptx` root module.

The finite add/multiply real bridges require a finite **result**. Finite inputs
alone do not prevent overflow. Their rounded-real target uses nearest-even with
gradual underflow and no upper exponent bound. The absolute error theorem is a
local rounding bound; the relative `2^-24` bound requires nonzero magnitude at
least the minimum normal value. Signed zeros merge under real interpretation.
NaN/infinity have no partial real interpretation; the total library projection
maps them to zero, so its finiteness guard must be retained.

The encoded library preserves bits and has its own deterministic NaN selection.
That is not automatically the allowed PTX NaN-result relation. The explicit-mode
refinement theorems preserve four IEEE rounding directions; the audited
TorchLean real-error bridge is specifically nearest-even. These checks prove no
PTX flush-to-zero rule, approximate instruction, runtime native replacement,
PyTorch correspondence, or GPU conformance. See the
[source and scope audit](../../../docs/formalization/numerical-foundation-audit.md).

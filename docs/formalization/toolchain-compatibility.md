# PTX foundation compatibility with Lean 4.34

The isolated experiment completed successfully on 2026-09-23. The entire current
PTX library builds under Lean 4.34 without changing any definition or proof.
The copied dependency audit reports 353 declarations, all using only the allowed
standard Lean axioms. During this isolated experiment the root toolchain remained Lean 4.33; its source
files and build cache were not changed by this experiment.

## Exact experiment

Copied `Ptx.lean`, every `Ptx/**/*.lean`, the Lake configuration and manifest,
and `scripts/check_proofs.py` into a fresh directory under `/tmp`. Changed only
its `lean-toolchain` from `leanprover/lean4:v4.33.0` to
`leanprover/lean4:v4.34.0`. No source patches, copied compiled artifacts,
TorchLean dependency, or dependency updates were used.

The actual compiler reported:

```text
Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
```

Commands run in the copied project:

```sh
lake build Ptx > build.log 2>&1
python3 scripts/check_proofs.py --scan
lake env lean --version
lake env lean Ptx/Audit.lean > audit.log 2>&1
python3 scripts/check_proofs.py --audit audit.log
```

All commands exited successfully. The source guard checked 31 Lean files; the
build completed 32 jobs; the audit checked 353 declarations. The root project's
own `scripts/check_proofs.py --audit` was also run against the copied audit log
and passed. A final hash comparison found no root source changes relative to the
snapshot, so both audit policy checks described the same captured source.

Three non-fatal warnings occurred in `Ptx/SharedVector.lean`, at lines 240, 383
and 407: `if_neg` is deprecated in favor of `ite_eq_right`. They require no
change for this build to pass. If a future build treats warnings as errors, those
uses need the routine spelling update. No other migration change was required.

## Provenance

The original copied inputs have the SHA-256 values below. The toolchain entry
records the original root file; the sole experiment substitution is stated above.
The canonical JSON object (sorted keys, compact separators) has SHA-256
`137680147bfcbfc16fc85c2e7d16a4a4b31753566138e7cfb9de4e6b57fec65e`.

```json
{
  "Ptx.lean": "092bb380c62d21c927a234b1a0ad0ddda75f5ecbb89b29e91a558207ae2e6307",
  "Ptx/Audit.lean": "f80abae0a357cf33981260ad6247fdcfd7b3f0b86c11b603375b1ecf47068eed",
  "Ptx/ByteExamples.lean": "776c20b110c210d21a24a97d6775c71b66532378f2d7d41656252943eff9f33b",
  "Ptx/ByteMemory.lean": "0c22fff3fd7d640e19414083fd576497cd04e201e6fb0b42fba77d9b626b6953",
  "Ptx/Checker.lean": "5cbe81accb2ebb47db7d42f4dddf49c22834f924a71eed49287a808f84159a36",
  "Ptx/CheckerExamples.lean": "cb7624ff5b2336813f5bced039adbdad7808bebcb3563c0a99dca62f652f42e1",
  "Ptx/ComputedPublication.lean": "a762aaacf8b5580df8a2b4cd1d7f5302851a4dee30dc7de23bf43cf7d1c9ef0d",
  "Ptx/ComputedPublicationMachine.lean": "d2d6bc8c8df7d5a684ba5f80f1b90658e9bb89fdcbb394ff65304c3bd05f1f5c",
  "Ptx/ComputedPublicationWitness.lean": "cc00dd30831f03b35fcf28b2af188e079fd06eea92f25a3b2c5cfad4d7baebb8",
  "Ptx/Environment.lean": "f2f1abd520b034cf68ed66a5a2b449ddd4f557eeebfe2f35b52c6c7c0e0219fe",
  "Ptx/IntegerMinMax.lean": "b821226d079b1c4ee8f5b7bf2d700cdf5fc74702823e28f30bb95d58035b3e42",
  "Ptx/Language.lean": "5a0bd03b96e861fd17272c8ad0f57bd448661b5f816a3c246e10c50f2887cc15",
  "Ptx/Litmus.lean": "58c07837ecb7b7c806feb36e7d5a3b5afdeaf82f510d37a63dd05aff90b1a9bc",
  "Ptx/Memory.lean": "6d23ee35dbf28c730e190c9cb675653caebb88cb21dad06c86edecb9fd358373",
  "Ptx/MessagePassing.lean": "8428bea332b97ebc4069ab3158f5b75d9236e48e43736d272544cf25243dba92",
  "Ptx/MessagePassingOutcomes.lean": "7624ae84a765d2479f66091522ca331a6fa88fe608add49164e8869a688e5ca3",
  "Ptx/Program.lean": "e1b96249c624c38590da8c62d35bc59d4234df789272a75da27dfd8c59d8ac1c",
  "Ptx/Publication.lean": "8a6c7c52996f95a2684199604e9e16e2b5d7a5f5be36ab67ff083a94767c6f68",
  "Ptx/Reachability.lean": "867562036b56fb5a8818f56d46f0feec33f197adf255b8a16c0e45ffbd81b8be",
  "Ptx/Scalar.lean": "84ba68d940e788ead9bfb8258a7bb0ada807ddecdb04f2d037d6e38bb11577d4",
  "Ptx/ScalarEnvironment.lean": "e6799aa2c5e85aaef0343fe8847a94a3a89539c0c3fe32482033cdabd4c77f57",
  "Ptx/ScalarExamples.lean": "c935dd51005184fdb47c9bab7a1d1b317977b69971d3febb8c80a9c5c3b889cd",
  "Ptx/ScalarKernels.lean": "d7ffcdefcd79ce591e68556a5267bbfaec00a459e3df936a40ceeae5a2803d2f",
  "Ptx/ScalarMemoryWitness.lean": "2bf71dd05a4e284354edd8e37f8bded72b0d4f269b6e7fc6090a0f4948879aae",
  "Ptx/ScalarRules.lean": "57a0dbf7a370f0d484cfdde5ad7c66963b14d7a9d6c4d4a2b0cd5b4bef236d9f",
  "Ptx/ScalarText.lean": "f9e14f54dbbf0fd4feedc6457fc3d329e47ad5cc07397c957c4da8aa210f8a34",
  "Ptx/ScopedExamples.lean": "2ef5d95b9af6f33734fb2b6f2653c60596b5ad4faaf7582df0ccecd7258c726e",
  "Ptx/ScopedMemory.lean": "d7d330431f415c855ca0d81edf5e4d857ae8dea1da66ed846f6d5af05761aa4d",
  "Ptx/SharedVector.lean": "2e0b17b7bc857f7251858e218acb3e21c4f1dfe0259f371b23f68c92dd0e19bc",
  "Ptx/SharedVectorExamples.lean": "35c8903aa0bce60b91fdcd9cd15a14d49de6f99b6c29f58a74429ca3861398cc",
  "Ptx/SharedVectorMemory.lean": "b1a35a5c3958cb683127c43a63acc473e86b4c7f40c8710c961b8215e6c4f716",
  "lake-manifest.json": "01f2e843d09759bcf28da5f401f7ad71f86b08c579e21227dcc076f31d9be719",
  "lakefile.toml": "0dd5039a9be123956d246a2d0134759ae33bb43c356b3b994b2c97478054e14d",
  "lean-toolchain": "302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b",
  "scripts/check_proofs.py": "15f138e83abe8cf809d6e5883203b5612c01db1ef598dcf533d15545b6bd71bc"
}
```

Build log SHA-256: `78fd7f63c754f2f8a44658b9d5ebf3e39f4aad25a9728a3cfba6f268a7192e9d`.

Audit log SHA-256: `a0024ab5d98101b54b6f78b7642304c7ff49019e1d3fee111349ae0f55602f27`.

Transient artifacts are in `/tmp/ptxlean-lean434-compat-9kdf9vp8` and are not
required as permanent dependencies. The source manifest above is the durable
identity of what was tested.

## What the isolated experiment establishes

This removes the source-compatibility obstacle to evaluating a root migration to
Lean 4.34. It does not itself migrate the root, validate all non-Lean project
checks under that migration, or prove successful joint linking with TorchLean.
After an explicit migration, the complete root checks must pass, and a separate
integration build must import both the actual PTX package and the pinned
TorchLean package. Rebuilding that combined graph may expose dependency or
configuration conflicts that an independent PTX build cannot detect.

Neither compiler compatibility nor a dependency audit establishes that the PTX
definitions faithfully represent NVIDIA's semantics, or that a numerical/PTX
bridge implements the TorchLean graph. Those remain separate proof and review
obligations.

## Subsequent migration and joint-library check

After the isolated experiment, the root pin was changed to
`leanprover/lean4:v4.34.0`. No PTX semantic definitions or proofs were changed for
the migration. The complete `scripts/check.sh` passed before further instruction
modules were imported: source provenance, coverage inventory, archived worker
evidence, Python tests, Lean source guard, library build and the 353-declaration
audit all passed. The same three deprecation warnings remained non-fatal.

The integration then added the actual root package as a local `ptxlean` dependency
and imported `Ptx` alongside pinned upstream TorchLean. Targeted
`lake update ptxlean` preserved every previously resolved upstream Git revision.
The combined `lake build PtxTorchLean` and fresh `lake env lean PtxTorchLean.lean`
passed. Six existing graph endpoints and the new
`unsigned_min_scalar_embedding` theorem report only the allowed standard Lean
axioms. The shared theorem embeds the unsigned value of the actual modeled PTX
minimum into a real TorchLean scalar. It checks joint elaboration; it is not a
proof that a PTX kernel implements the neural-network graph.

The separate [joint verification receipt](../../integration/torchlean/verification-joint.json)
records all tested root and integration source hashes and command outcomes. The
[initial isolated receipt](../../integration/torchlean/verification.json) and the
source manifest above remain historical evidence for their original inputs.
Later changes to either package require new checks.

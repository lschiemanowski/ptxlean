# PTX ISA 9.4 source reference

The project does not redistribute NVIDIA's manual. Obtain it directly from
[NVIDIA](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).
The reviewed source is identified by SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.

`manifest.json` records the original and resolved URL, UTC retrieval time,
response metadata, byte count, SHA-256, and 23 section references. These are
locators and provenance, not copies of the instruction descriptions. The
`index.html` artifact name and line/byte positions refer to the exact reviewed
HTML; they do not promise that the live website remains unchanged.

From the repository root, explicitly acquire and verify a local copy:

```sh
python3 scripts/check_sources.py --fetch
```

The command downloads HTML as data, verifies the pinned digest and byte count,
and only then saves `.ptx-source/9.4/index.html`. That cache is ignored by Git.
It installs no software and executes none of the downloaded content. Ordinary
checks require this file and never download it implicitly. If NVIDIA's URL no
longer supplies those exact bytes, verification fails instead of accepting a
new version. An already acquired exact copy can be installed with
`python3 scripts/check_sources.py --from-file PATH`.

`SHA256SUMS` records the same digest using the original artifact name. Section
links in project explanations point to NVIDIA's website for reading; exact-source
checks use the local verified copy. The vendor document remains subject to its
own notices and terms. The project's license applies to project code, not to
NVIDIA's documentation.

The manifest does not claim that any instruction passage is self-contained or
that its references cover all shared rules needed for full PTX verification.
See the [source ledger](../../../docs/foundations/source-ledger.md) for the
project's interpretations and explicit restrictions.

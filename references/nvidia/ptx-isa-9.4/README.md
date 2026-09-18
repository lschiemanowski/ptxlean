# PTX ISA 9.4 source snapshot

`index.html` is the unmodified HTML response downloaded from
[NVIDIA's PTX ISA manual](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).
The document identifies itself as PTX ISA 9.4. Its bytes, rather than the changing
live URL, identify the source used by the foundations study.

`manifest.json` records the original and resolved URL, UTC retrieval time,
response metadata, byte count, SHA-256, and 23 section references. Each reference
has the original heading and anchor, a local fragment URL, and a line number in
the frozen HTML. Line numbers are locators within these exact bytes, not a
promise about a later NVIDIA publication. ETag and Last-Modified are recorded
server metadata; the SHA-256 is the content identity.

From this directory, verify the source offline:

```sh
sha256sum -c SHA256SUMS
```

Expected result: `index.html: OK`.

The snapshot contains the HTML text and embedded code, including NVIDIA's
notices. Linked figures, stylesheets, scripts, and other documents have not been
mirrored, so this is not a self-contained rendering of the entire documentation
site. The study uses text and code sections in this file. A later source update
requires a new content identity and review of affected interpretations; do not
silently overwrite this snapshot. The vendor document retains its original
copyright and notices; the repository's license does not replace them.

The manifest is a locator inventory, not a semantics extractor. It does not
claim that an instruction description is self-contained or that its links cover
every shared rule needed for full PTX verification.

See the [message-passing study](../../../docs/foundations/message-passing.md)
and [representation proposal](../../../docs/foundations/representation.md).

# Plain byte-permutation source review

This review concerns `prmt.b32` in the pinned PTX ISA 9.4 manual, section
`data-movement-and-conversion-instructions-prmt`, with manual SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Source text is reconstructed from the verified local cache and is not distributed.

The source numbers the eight input bytes from the first word's least significant
byte through the second word's most significant byte. Output bytes are numbered
from least to most significant. Each uses the corresponding four-bit selector
from the control's low sixteen bits. A selector's low three bits select a byte;
its high bit requests replication of that byte's most significant bit instead of
copying the byte. Replication produces zero for a clear sign bit and 255 for a
set sign bit. It does not copy only that sign bit into one position.

The all-input law observes a result bit j. Output byte j/8 uses the control
selector at bit position 4*(j/8), masked to four bits. Selector values 0..3 choose
the first word, 4..7 the second; the same source choices repeat for 8..15 with
sign replication. Within the selected word, selector modulo four picks the byte.
Ordinary copying uses bit j modulo eight; replication uses bit seven. This is
independent of the worker's chosen computation representation.

Only output bits below 32 are observed by the required law, so it uses four
selectors. No range premise restricts the control word: arbitrary upper control
bits must have no effect. Unlike LOP3's lookup-table parameter, PRMT's control is
a runtime word operand, which may name a register or carry an already converted
immediate. It participates in operand reads, aliasing and event metadata.

The selected plain form was introduced in PTX 2.0 and requires SM20 or higher.
The model uses ISA exactly 9.4 and a numeric SM feature floor of 20, even for a
skipped fetched instruction. It does not validate architecture spellings.
Specialized modes use different control interpretation; all six are excluded,
rather than approximated by the plain form. Their actual spelling places the
mode after `.b32`, as checked by the rejection examples.

The existing Pure32 engine reads every source in the incoming state and allows
repeated registers and overlap with the destination. Enabled steps update only
the destination and program counter; skipped steps advance only the counter.
Occurrences retain ordered source reads and the guard read, or just the guard
when skipped. No memory, address, predicate or other word register is changed.
The typed decoder must characterize exactly the admitted spelling and operand
shape in both directions. It assumes compatible declared 32-bit operands and
already converted literals, and does not validate raw PTX modules.

The driver checks the exact arbitrary-input theorem signatures, including the
output-bit law, frame, origin, one-step existence, determinism and exact decoder
round trips. An additional byte-level integer oracle supplies concrete expected
words independently of the reference fixture's per-bit construction. Deliberate
compiling faults test whether the driver detects changes to source ordering,
sign replication and selector masking. These checks support source review;
they do not prove that all possible semantic mistakes are detected.

Final source/statement review and fresh replay are recorded with the actual
worker result. A proof about a candidate definition and evidence that it faithfully
represents PTX remain separate, and neither establishes GPU conformance.

The submitted worker computation constructs a word from 32 Boolean observations,
using the exact selector, source-word and bit-position rules above. Its bit law
uses the existing library's list-to-bit-vector observation facts. All operands
are still evaluated in the incoming state, and the decoder admits full-width
control registers and immediates without an extra range condition. Inspection of
the proof statements found no additional premises hiding a result or execution
obligation. The worker reused accepted leaf patterns; its recorded commands do
not show a read of the manual section, so this is not evidence of independent
source interpretation by the worker.

The separate GLM reviewer accepted with no findings. Its target explanation uses
version-floor language: PTX 2.0 is the instruction's introduction version, while
the actual formal predicate selects exactly ISA 9.4. That distinction is retained
in the contract and ledger; the model does not claim support for all versions
since 2.0. The coordinator reviewed actual definitions and statements separately
from that advisory verdict.

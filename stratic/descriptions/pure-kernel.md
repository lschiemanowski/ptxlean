# Composing pure instructions into kernels

A kernel program can interleave the existing scalar instructions with instructions
from several reviewed pure families. Scalar instructions supply memory accesses,
branches and exit; pure families supply their own permitted result relation.
One scalar state holds the registers, program counter and word memory throughout.
Adding a family does not require changing the execution rules for other families.

The execution domain is a single thread over supplied, aligned word storage,
using the scalar arena's concrete memory reads. It selects PTX ISA 9.4 and
numeric SM at least 70 for the scalar relaxed GPU-scope memory forms. Every fetched
pure instruction additionally checks its own family's target condition, including
when its guard is false. An unsupported domain or family target is reported as
unsupported, not silently treated as successful termination or as a PTX behavior.
Missing instructions and bad memory accesses retain explicit faults.

Every permitted pure result remains an available transition; composition does
not choose one result or assume determinism. A finite advancing trace is a prefix,
not a terminated run. A run must end with exit or an explicit failure. Trace
composition, instruction origin, memory bounds and unchanged memory outside
actual stores follow from the constituent transitions. Existence of a next step
is separate from termination of a program containing branches.

The shared finite-path rules are also used by the scalar/binary32 execution
model. Connections to older scalar operations prove equality of their state
changes and corresponding event fields where operations overlap. A typed family
and a scalar instruction remain distinct instruction identities.

This composition does not admit general concurrent PTX executions, validate raw
modules or register declarations, or establish GPU/runtime correspondence.

For a catalog whose result relation is proved deterministic, a completed
halting run also controls all finite execution prefixes: each prefix extends
to the same run and contains fewer events than the complete trace, which
includes exit. This gives a reusable way to rule out infinite advancing
executions when a concrete kernel supplies a finite halting witness. It does
not assume determinism for other catalogs or establish GPU scheduling progress.

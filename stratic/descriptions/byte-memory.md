# Byte-level scoped observations

Each byte read records a compatible source write and the corresponding byte
value. Access widths, overlap, endianness, initialization and scope membership
are explicit. The first model retains aligned fixed-size accesses and excludes
mixed-size overlap and additional proxies.

The source-reviewed single-copy constraints apply exactly to their qualified
operation pairs. Out-of-scope races are not forced to observe an entire word
from one write. Examples construct permitted torn candidates and prove rejection
where the relevant atomicity and ordering requirements forbid them.

A checked specialization explains the relationship to the existing whole-word
model. Sufficient conditions for uniform sources are distinguished from mere
value equality and from an unconditional claim of equivalence. The scope and
limits of any completeness claim are explicit. Dependent concurrent no-thin-air
semantics is a separate obligation, not an invented syntactic cycle condition.

Where source wording leaves the observation relation for torn reads unsettled,
named interpretations remain explicit. Results claimed independent of that
choice are proved for each interpretation; no chosen convention is presented
as a settled translation of PTX.

# Source review: environments and scalar execution

This review uses the [pinned PTX ISA 9.4 manual](../../references/nvidia/ptx-isa-9.4/README.md).
It records source interpretations and boundaries for the environment and scalar
execution work. It is not a proof of correspondence between NVIDIA's prose and
Lean. The existing [source ledger](source-ledger.md) describes the narrower
immediate-store fragment; its dependency restrictions must not silently disappear
when register stores, address calculations, or branches are introduced.

## Topology, scopes, and storage

[Thread hierarchy][hierarchy] and [scope][scope] give separate responsibilities:

- A thread belongs to a CTA, a grid, and a device; an explicit or implicit
  cluster groups CTAs. CTA and cluster identifiers are local to their containing
  launch. Equal numeric identifiers in different grids must not imply shared
  membership.
- CTA scope includes the issuer's CTA. Cluster scope includes its cluster. GPU
  scope also includes other grids from the same program on that device. System
  scope extends to the program's other devices and host threads. A device-only
  thread universe is therefore a restricted interpretation of system scope.
- A warp is not a memory scope. Scope membership does not imply lockstep
  execution, scheduling fairness, or a barrier.
- Cluster support requires an eligible `sm_90`-or-later target. Cluster scope and
  the explicit shared-space subqualifiers were introduced in PTX 7.8. The
  ordinary scoped relaxed/acquire/release load/store forms require PTX 6.0 and
  an eligible `sm_70`-or-later target. These thresholds do not constitute a
  validator for every PTX opcode or architecture-specific target family.

[State-space access][spaces] is independent of synchronization scope. Local
storage belongs to one thread. Shared storage belongs to a CTA and can be
accessed by active peer CTAs in its cluster through the appropriate shared
addressing form. The source explicitly requires establishing that a peer CTA's
storage exists and remains alive until the access completes. `shared` without a
subqualifier means `shared::cta`; `shared::cluster` is a distinct addressing
form. Merely giving an access system scope cannot grant access to another
thread's local storage or a different cluster's shared storage.

Global storage is shared within its context. Constant storage is read-only.
Kernel parameters are per-grid read-only inputs; device-function parameters
have different access and ABI rules. A coarse ownership model may expose these
categories without implementing their complete addressing or calling convention.
That distinction must be stated explicitly.

Declared global and constant variables default to zero when their declarations
have no initializer. This does not justify initializing all allocations or
registers to zero. The [memory initialization rule][initialization] assigns an
unknown but fixed initial byte value where no program initializer is given.
Explicit initial register assignments are execution inputs or proof premises,
not a PTX zero-initialization rule.

## Addressing and access legality

[Address operands][addresses] are byte addresses. Natural alignment is to the
whole instruction access size, and misalignment has undefined behavior in the
source; it is not permission to silently round every address down. A safe
fragment can reject misalignment while identifying that result as exclusion of
undefined behavior. A mathematical arena bound is distinct from actual
allocation, lifetime, and finite-pointer validation.

PTX addresses can be 32 or 64 bits. The source describes extension and truncation
relative to the target state-space address width. Register arithmetic and
address-space conversion are distinct operations. An implementation supporting
only a fixed-width explicit global address form must not claim the entire
generic-addressing or ABI behavior. [Generic addressing][generic] involves
state-space windows; identity mapping is an explicit restriction, not the
general rule. Virtual addresses, underlying storage identity, and private-space
ownership must remain distinguishable when aliasing is supported.

The [load][ld] and [store][st] sections make the default memory qualifier weak.
Omitting a qualifier must not silently produce a relaxed access. Relaxed and
acquire loads, and relaxed and release stores, apply only to global/shared
storage, including generic addresses that resolve there. Volatile, cache,
readonly-proxy, MMIO, vector, and wider-register forms have further rules.
Rejecting an unsupported qualifier is preferable to accepting it with unrelated
semantics. Stores to constant memory are illegal.

The selected textual `st` forms take their data from a register. A constant
publication is represented in source PTX by a register move followed by that
store. The older immediate-store event language is a normalized memory-only
representation; its constant operand is not a claim that literal-store PTX
syntax is accepted. The scalar machine retains an internal immediate-store
convenience, but the typed PTX decoder rejects it and the supported-text
round-trip theorem excludes it. The addition lane instead computes its value in
a register and stores from that register; its trace witness does not substitute
a constant-store instruction for the executed computation.

## Scoped memory relations

The old all-GPU, same-device restriction made all matching program accesses
mutually in scope. Removing that restriction requires more than attaching a
scope field to the old events.

[Morally strong operations][morally] require program-order relatedness or
mutually inclusive scopes on strong operations, together with the proxy and
overlap requirements. One operation including the other thread is insufficient
if the reverse inclusion fails. Storage accessibility is an additional premise.

[Coherence][coherence] is total only for the overlapping write pairs for which
the source requires a relation: morally strong or causality-ordered pairs.
Overlapping writes in a data race are unrelated in coherence. Therefore the old
same-word totality condition cannot be reused unchanged for arbitrary scopes.
The source still describes programs with uniform-size races; the
[mixed-size-race exclusion][races] must not become a blanket rejection of every
race. Initialization ordering remains a separately documented normalization.

The three causality constructions remain distinct. Scope affects which
synchronization edges exist; it does not replace proxy preservation or justify
transitively closing the final causality relation. A scoped candidate satisfying
these relations is not, by that fact alone, a complete semantics for dependent
programs.

There is an additional byte-level boundary even before dependencies are added.
The [single-copy atomicity guarantee][atomicity] depends on morally strong
read/write pairs. Matching widths alone do not supply that guarantee when their
scopes exclude each other. Reusing one whole-word source per read therefore
restricts the generalized scoped model to **non-torn candidates**. An
outside-scope stale-read witness remains meaningful, but its existence does not
establish that every permitted outcome has been represented. Universal claims
over that restricted candidate model cannot automatically be promoted to all
PTX executions. Byte-level sources, or a separately justified condition ensuring
the required atomicity, are needed to remove this restriction. Exact
specialization to the original all-in-scope fragment is a different, narrower
claim and remains possible.

## Scalar instruction interpretations

| Form | Source-reviewed interpretation | Boundary |
| --- | --- | --- |
| Unsaturated `add.u32/u64`, `sub.u32/u64` | Fixed-width unsigned arithmetic; discarded overflow is represented by bitvector arithmetic. | Saturation, carry flags, signed and packed operations have separate contracts. |
| `mul.lo.u32/u64` | Retain the low operand-width bits of the full product. | `.hi` and `.wide` are distinct; `.wide.u64` is not an available integer form. |
| Register/immediate `mov`, `cvt.u64.u32` | Preserve the moved bit pattern; the unsigned widening conversion preserves the numeric value by zero extension. | Taking symbol addresses, special-register reads, other conversions, and ABI operations require separate contracts. |
| `and`, `or`, `xor`, `not` on bit words | Bitwise operations at the selected width. | Predicate forms require predicate operands rather than implicit numeric conversion. |
| `shl.b32/b64`, unsigned/bit `shr` | Shift count is an unsigned **32-bit** operand for both data widths. Counts at or above the data width produce zero. | Do not mask counts modulo the word width. Signed right shift has sign-fill behavior. |
| Unsigned `setp` | Equality/inequality and unsigned order; `lo/ls/hi/hs` alias the corresponding unsigned order comparisons. | Bit-size types admit only equality/inequality. Dual destinations and Boolean-combination forms need their own handling. |
| Guarded instruction | A false guard skips the instruction's effects; a true guard executes its normal operation. | Skipped memory instructions must not emit an access or fault by eagerly executing the memory operation. |
| `bra` | An enabled branch changes the program counter to its label; a disabled guard falls through. | `.uni` asserts warp-wide uniformity, so cannot be accepted merely as ordinary scalar branching. |
| `exit` | Terminates the executing thread. | In full PTX it also affects barriers waiting only on exited threads. A local halted state is a restricted no-barrier interpretation. |

These interpretations come from [integer arithmetic][integer],
[moves][mov], [conversion][cvt], [bit operations][logic], [shifts][shifts], [comparison][setp],
[predication][predication], [branch][bra], and [exit][exit]. A parser or printer
must preserve the supported instruction's width, qualifier, predicate, and
address form. A subset printer is not automatically a parser for arbitrary PTX
or a complete runnable module generator.

## The no-thin-air obstacle

[PTX 9.4's no-thin-air clause][nta] is a semantic restriction on self-justifying
speculation. It is not given as a complete syntactic dependency algorithm.
Two details prevent a naive extension of the earlier graph model:

1. In the load-buffering example with register-dependent stores, a cycle in
   reads-from and instruction dependence may carry the initialized zero value.
   The source forbids invented nonzero values, not every such cycle.
2. The source allows implementations to use arbitrary reasoning to show that
   apparent dependencies are semantically unnecessary. Dependency-free cyclic
   communication must remain possible where permitted by the other rules.

Consequently, acyclicity of reads-from plus conservatively tracked dependencies
can be a sufficient execution discipline, but it is not an exact replacement
for PTX's clause. Tracking only register-value dependencies also misses
address dependence and control dependence that determines which stores occur.
Local oracle consistency alone is insufficient: mutually dependent threads can
agree on an invented value while each local trace is internally consistent.

An implementable foundation keeps these claims separate:

- A scalar local machine defines instruction transitions, dynamic occurrences,
  control flow, and memory effects. Its oracle-driven runs are candidates until
  all required global conditions have been discharged.
- Memory-order constraints without a complete no-thin-air account can provide
  an explicit **overapproximation** for universal safety or functional proofs.
  Proving a kernel correct for that larger candidate set is useful. Accepting a
  candidate from it does not establish a permitted PTX execution. This argument
  requires retaining every behavior permitted by the other clauses; for example,
  the non-torn scoped representation above is not such an overapproximation
  where PTX permits byte mixtures.
- Constructive sequential execution, or a separately justified grounding
  discipline, supplies useful existence results for a supported subclass.
  Read-only inputs and disjoint output ownership can prevent the problematic
  cyclic communication in practical scalar kernels. The necessary separation,
  initialization, and address premises must appear in their contracts.
- A sufficient subclass cannot justify claiming that all PTX executions have
  been characterized. In particular, rejecting permitted zero-valued dependency
  cycles must be acknowledged if a dependency-acyclic discipline is selected.

A sequential machine alone is not a replacement for the relational concurrent
semantics. Its finite runs, safety results, and kernel computations can be
proved directly, while any relationship to broader PTX executions is a separate
theorem or explicitly open correspondence obligation. This is a substantive
remaining semantic problem, not a proof obligation to hide inside a predicate
named `Valid`.

[hierarchy]: ../../references/nvidia/ptx-isa-9.4/index.html#thread-hierarchy
[scope]: ../../references/nvidia/ptx-isa-9.4/index.html#scope
[spaces]: ../../references/nvidia/ptx-isa-9.4/index.html#state-spaces
[initialization]: ../../references/nvidia/ptx-isa-9.4/index.html#initialization
[addresses]: ../../references/nvidia/ptx-isa-9.4/index.html#addresses-as-operands
[generic]: ../../references/nvidia/ptx-isa-9.4/index.html#generic-addressing
[ld]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld
[st]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st
[morally]: ../../references/nvidia/ptx-isa-9.4/index.html#morally-strong-operations
[coherence]: ../../references/nvidia/ptx-isa-9.4/index.html#coherence-order
[atomicity]: ../../references/nvidia/ptx-isa-9.4/index.html#atomicity-axiom
[races]: ../../references/nvidia/ptx-isa-9.4/index.html#mixed-size-limitations
[integer]: ../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions
[logic]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions
[mov]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-mov
[cvt]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-cvt
[shifts]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-shl
[setp]: ../../references/nvidia/ptx-isa-9.4/index.html#comparison-and-selection-instructions-setp
[predication]: ../../references/nvidia/ptx-isa-9.4/index.html#predicated-execution
[bra]: ../../references/nvidia/ptx-isa-9.4/index.html#control-flow-instructions-bra
[exit]: ../../references/nvidia/ptx-isa-9.4/index.html#control-flow-instructions-exit
[nta]: ../../references/nvidia/ptx-isa-9.4/index.html#no-thin-air-axiom

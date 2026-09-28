# PTX version and entry correspondence

The formal project remains pinned to PTX 9.4. The first hardware adapter emits
only the older instruction forms used by `Dense.Compact.program`, plus explicit
entry setup. It does not change the formal instruction definitions or target.

On the initial validation machine, CUDA 13.2 `ptxas` accepts PTX 9.2 and rejects
`.version 9.4`. Driver 610.57.04 likewise returns
`CUDA_ERROR_UNSUPPORTED_PTX_VERSION` for a minimal 9.4 module. Therefore the
recorded run explicitly uses `--ptx-version 9.2 --target sm_120` on an RTX 5090.
The default remains 9.4; there is no automatic downgrade. This is evidence for
the documented common instruction subset, not a claim that the machine ran a
9.4 artifact.

The [archived PTX 9.2 manual](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html)
was compared with the project's locally pinned 9.4 manual. The
[comparison receipt](receipts/ptx-version-compatibility.json) retains URLs,
whole-document hashes, section hashes and review conclusions; it contains no
vendor description text. Integer multiplication, floating-point addition and
multiplication, comparisons, shifts, bitwise AND, movement, barriers, exit and
thread/group identity sections have equal normalized text. The differing
sections concern unrelated packed forms, newer memory qualifiers, floating-point
conversions or editorial changes. The plain forms below are unaffected by those
changes. This is a source review, not a formal cross-version refinement proof.

| Formal body operation | Emitted form | Correspondence |
| --- | --- | --- |
| Integer movement/arithmetic | `mov.b32`, `add.u32`, `mul.lo.u32`, `and.b32`, `shr.u32` | Same 32-bit words; no numerical conversion |
| Widening and address addition | `cvt.u64.u32`, `add.u64` | Address registers remain byte offsets |
| Unsigned comparisons | `setp.lt.u32`, `setp.eq.u32`, `setp.ge.u32` | Same predicate; ReLU uses the encoded sign test |
| Binary32 arithmetic | `mul.rn.f32`, `add.rn.f32` | Explicit nearest-even rounding, separate operations, no `.ftz` |
| Memory | `ld/st.relaxed.gpu.global.b32`, `ld/st.relaxed.cta.shared.b32` | Predicated base-plus-offset address followed by the same predicated access, with the model’s explicit relaxed ordering and scope |
| Group barrier | `bar.sync 0` | Every thread reaches each site; no optional count or divergent early exit |
| Exit | `exit` | Thread ends after its output phase |

The entry wrapper obtains the global arena base with `ld.param.u64`, the shared
allocation's address with `mov.u64`, and physical row/thread identities from
`%ctaid.x` and `%tid.x`. It puts `row*2^depth+lane` in word register zero using
`shl.b32` and `add.u32`. This matches `GridDense.thread` and `Dense.controlSeed`.
The runner launches one group per row and exactly `2^depth` threads per group;
`.reqntid` declares the required group dimensions in the PTX.

Each thread zeros its own word in every shared plane, then all threads synchronize.
This establishes the zero shared array in `GridDense.initial` before entering
the emitted body. Other working registers remain unspecified, as allowed by the
formal entry state. Their needed values are initialized by body instructions.
Address relocation uses separate temporary registers so it does not overwrite
modeled offset registers. The shared base identifies this group's allocation;
the global base identifies the single input/output arena. Host guard words
surround that arena and must remain unchanged.

The manifest maps every formal instruction position to its Lean representation
and emitted PTX statements. The body comes directly from the existing Lean list;
the Python wrapper does not reconstruct the reduction. `ptxas --fmad=false`
and explicit rounding preserve the intended separation of multiply and add at
the PTX interface. Neither serializer, entry wrapper, CUDA API adapter nor NVIDIA
compiler is formally verified by this milestone. Bit comparisons, rational
bounds and sanitizer checks are empirical evidence about this connection.

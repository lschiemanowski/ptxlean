# Four manually supplied backward kernels

For the scalar real network `y=(x*w+b)^2`, an incoming output weight `d`
asks for the sensitivities `dx=2*d*(x*w+b)*w`, `dw=2*d*(x*w+b)*x`, and
`db=2*d*(x*w+b)`. This module is the separately authored kernel execution
layer. It receives an encoded saved affine value `A`. Relating that value to
a cache-free forward execution, and comparing rounded answers with the real
sensitivities, are separate obligations; neither is assumed by its execution
theorems.

The module reuses the actual seven-instruction affine program: three loads,
rounded multiplication, rounded addition, store, and exit. The chosen four
launches compute `q=2*d+0`, `db=q*A+0`, `dx=db*w+0`, and `dw=db*x+0`.
Positive-zero additions are real operations; the implementation does not
silently collapse them into multiplication. All eight rounded result choices
remain visible in `Results`.

| Word index | Initial contents | Final contents |
| --- | --- | --- |
| 0–3 | x, w, saved A, d | unchanged |
| 4–5 | binary32 +2 and +0 | unchanged |
| 6–9 | arbitrary old dx, dw, db, q | actual dx, dw, db, q |
| 10 onward | arbitrary tail | unchanged |

The exact +2 bits are `0x40000000`; +0 is `0`. Address arguments are byte
offsets, so a word index is multiplied by four. `arguments` binds the four
launches to `[16,12,20,36]`, `[36,8,20,32]`, `[32,4,20,24]`, and
`[32,0,20,28]`. These lists select the two multiplicands, bias, and output.
Intermediate q and db pass through the real stored snapshot. Each launch has
its own arbitrary `Sequential.Seed` of starting registers and predicates;
these register seeds are unrelated to the mathematical incoming weight d.

`stage_run_iff` specializes the universal affine execution theorem to each
stage. `stage_launch_correct` then uses the actual serialized launch's run
and writeback to derive its arithmetic results, full final state, seven-event
trace, and new stored snapshot. `launches_correct` applies that fact four
times, passing the derived snapshots between launches. No stage receives an
assumed desired output. `pipeline_correct` packages the final consequence
for any admitted four-launch `Chain`.

Conversely, `pipeline_of_results` constructs all four actual launches for
any eight permitted rounded result words. `pipeline_exists` obtains those
words from the all-bit arithmetic existence theorem and discharges that
construction premise. Existence therefore covers NaNs, infinities and arbitrary
old outputs as well as finite inputs. It does not assert a finite answer or
an error bound for those inputs.

`stage_trace_safe` exposes the seven fetched program counters and instructions
and proves every projected memory access passes the derived live allocation
checks. `pipeline_memory_frame` and `pipeline_other_allocation` preserve
inputs, constants, extra words and unrelated allocations. The stage rejection
theorem inherits permanent rejection of a released logical allocation ID,
even after further valid storage transitions.

These are proofs in the existing one-thread serialized launch contract, with
ISA 9.4 and the numeric sm_70-or-later feature guard. A real runtime must supply
completion and memory visibility between launches, valid parameter binding,
and exclusion of interfering accesses. PTX thread exit does not establish
those runtime properties. Each local kernel retains the affine execution and
memory-witness restrictions; no combined cross-kernel PTX memory graph or
hardware NaN realization theorem is claimed. TorchLean automatic differentiation
does not generate this instruction sequence.

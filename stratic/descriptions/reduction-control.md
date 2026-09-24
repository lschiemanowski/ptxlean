# Reduction control and source qualification

A waiting thread has already arrived at the reduction's one barrier and cannot
execute its later instructions yet. In every state reached from the supplied
program start, a recorded arrival must belong to a live thread still positioned
at that exact barrier instruction. Repeatedly scheduling that waiting thread
leaves it waiting without creating another arrival. When the last participant
arrives, every thread is at that same site, so releasing them together to the
continuation does not skip any thread's computation or revive an exited thread.
This is a property of actual fetched steps, not an assumption about a schedule.

The program's instruction classification also matters: local arithmetic and
control instructions cannot create memory accesses, and instructions labelled
as memory operations must actually be loads or stores in their stated space.
The proof applies to instructions fetched from this fixed program; the more
general dispatcher is not independently a PTX instruction validator.

The machine computes target-neutral candidate executions. Interpreting these as
the selected PTX source slice requires ISA 9.4 and the `sm_70` numeric feature
floor for explicit relaxed memory operations. This target condition does not
validate all architecture spellings or prove correspondence to a GPU launch.
Shared addresses must fit the state space width; the example's no-wrap and
bounds conditions keep its actual shared offsets below 2^32 even though the
local address-register carrier has 64 bits.

These control results do not establish memory visibility or the reduction's
final sum. Those require the separate actual memory projection, ordering and
program arithmetic results. Individual arrival bookkeeping specializes the
full-participation, no-pre-barrier-exit case; it is not a general refinement of
warp arrival dynamics or a fairness guarantee.

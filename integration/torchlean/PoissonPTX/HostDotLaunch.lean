import PoissonPTX.HostDotLayout

namespace PtxTorchLean.Poisson.PTX.Host
open Concurrent

/-- Each reduction executes its actual 256-lane instruction program and nine
barrier rounds. Source choices belong to that same history and obey the
existing necessary repeated-barrier admission rule. -/
def DotLaunch (a : Layout n e w) (kind : DotEntry) (memory output : Memory) : Prop :=
  ∃ regs final events indices source,
    NativeFlow.Runs ⟨0,by decide⟩ a.dotContext (a.dotCode kind) (a.dotStart memory regs) events indices final ∧
    (∀ t, final.halted t=true) ∧
    Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) events source ∧
    Visibility.Repeated.OrderedSources events source ∧
    output=GlobalPublication.publish memory events

/-- Reduction existence is constructed from the physical arrays and shared
allocation, including all real barriers, the global store and all returns. -/
theorem dot_exists (a : Layout n e w) (kind : DotEntry) (memory : Memory) :
    ∃ output, DotLaunch a kind memory output := by
  have valid := a.scalar.valid64 kind.output kind.output_width
  have fits := a.scalar.fit kind.output
  rw [kind.output_width] at fits
  have room : a.base.toNat+(a.offset (.scalar kind.output)).toNat+8≤2^64 := by
    have := a.noWrap
    change (a.offset (.scalar kind.output)).toNat+8≤a.bytes at fits
    omega
  obtain ⟨final,events,indices,source,actual,done,compatible,ordered,_⟩ :=
    Dot.Witness.complete_published (cfg:=⟨0,by decide⟩) (ctx:=a.dotContext)
      (initial:=fun space => match space with | .global => memory | .shared => fun _ => 0)
      (a.dotStart memory (fun _ _ => 0))
      (fun _ => rfl) (fun _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl) a.dot_lane
      a.small (a.dot_arrays kind memory (fun _ _ => 0))
      (by decide : (0 : Word).toNat%8=0) (fun _ => ⟨rfl,by change 2048≤2048; decide,by change (0:Nat)+2048≤2^64; decide⟩)
      (fun _ => by
        change Valid64 a.base.toNat a.bytes (a.base+a.offset (.scalar kind.output)).toNat
        rw [Dot.output_address room]
        exact valid)
      (a.dot_apart kind) room
  exact ⟨_,(fun _ _ => 0),final,events,indices,source,actual,done,compatible,ordered,rfl⟩

variable {n e w : Nat} {a : Layout n e w}

theorem dot_frame (actual : DotLaunch a kind memory output) :
    a.Writes [.scalar kind.output] memory output := by
  obtain ⟨regs,final,events,indices,source,run,done,compatible,ordered,rfl⟩ := actual
  intro byte outside
  have bound := outside (.scalar kind.output) (by simp)
  have bound : byte<a.scalar.slot kind.output ∨ a.scalar.slot kind.output+kind.output.width≤byte := by
    simpa [Layout.slot,Layout.scalar,Scalar.Arena.slot,Field.count,Field.width] using bound
  rw [kind.output_width] at bound
  apply Dot.publication_outside run (by intro t h; simp [Layout.dotStart,Ptx.Barrier.reset] at h)
    (fun _ => rfl) (fun _ => rfl) (List.Perm.refl _) 
  have address := a.scalar.address kind.output
  simp only [Layout.scalar,Scalar.Arena.slot] at address bound
  rw [address]
  exact bound

theorem dot_static (actual : DotLaunch a kind memory output) : a.Static memory output := by
  apply (dot_frame actual).static
  intro f member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst f
  cases kind <;> rfl

end PtxTorchLean.Poisson.PTX.Host

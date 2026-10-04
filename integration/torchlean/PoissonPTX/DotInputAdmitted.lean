import PoissonPTX.DotInputObservations
import PoissonPTX.ObservedReplay

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- An allocated input field does not overlap the one output word. The two
input fields may overlap each other, including a self-dot-product. -/
def OutputApart (count : Nat) (left right output : Word) : Prop :=
  ∀ off∈[left,right], output.toNat+8≤off.toNat ∨ off.toNat+count*8≤output.toNat

theorem output_address {base output : Word} (room : base.toNat+output.toNat+8≤2^64) :
    (base+output).toNat=base.toNat+output.toNat := by
  simp only [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem input_word_separate (word : InputWord base count left right a)
    (apart : OutputApart count left right output)
    (room : base.toNat+output.toNat+8≤2^64) :
    (base+output).toNat+8≤a.data.address ∨ a.data.address+8≤(base+output).toNat := by
  obtain ⟨_,_,off,member,k,inside,location⟩ := word
  rw [location,output_address room]
  have separated := apart off member
  omega

/-- The input snapshot is recovered from the *whole* concurrent memory
history. Actual output-address and input-footprint proofs exclude every store
as a source of an input byte; no read value or local execution is assumed. -/
theorem admitted_input
    (whole : NativeFlow.Runs cfg ctx (program count left right output scratch) start events allIndices final)
    (aligned : Aligned start.core) (entry : ∀ owner, (start.core.lanes owner).pc=0)
    (arena : ∀ owner, (ctx owner).arena=base)
    (sameInitial : (start.core.lanes owner).global=initial .global)
    (compatible : Visibility.Compatible initial events source)
    (run : Flow.Observed.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
      (NativeFlow.lane start owner) words indices next)
    (recorded : ∀ a∈words, Event.data owner a∈events)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (inputsFit : ∀ off∈[left,right], base.toNat+off.toNat+count*8≤2^64)
    (outputFits : base.toNat+output.toNat+8≤2^64) :
    Flow.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
      (NativeFlow.lane start owner) next := by
  obtain ⟨footprints,noIndices⟩ := input_observations run (entry owner) bounded
    (by rw [arena owner]; exact inputsFit)
  subst indices
  apply Flow.Observed.replay (initial:=(start.core.lanes owner).memory) run
  · intro a member read
    obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp (recorded a member)
    have footprint := footprints a member
    have readonly : Visibility.ReadOnly events a.space a.data.address := by
      rw [footprint.1]
      apply readonly_input whole aligned entry
      intro thread
      rw [arena thread]
      apply input_word_separate _ apart outputFits
      simpa only [arena owner] using footprint
    have value := Visibility.read_only_value compatible found read readonly
    simpa only [footprint.1,PTX.State.memory,sameInitial] using value
  · simp
  · constructor
    · intro w member store
      have noStore := (footprints w member).2.1
      rw [noStore] at store
      cases store
    · simp
  · exact ⟨fun _ _ _ => rfl,by simp⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

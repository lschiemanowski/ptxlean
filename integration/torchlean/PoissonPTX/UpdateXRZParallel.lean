import PoissonPTX.UpdateXRZSources
import PoissonPTX.ObservedTemporalReplay
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

def Arena.value (a : Arena n) (memory : Memory) (field : Field) (i : Fin n) : Float :=
  let v := fun f => decode (read64 memory (a.slot f i))
  let alpha := decode (read64 memory (a.base.toNat+a.alpha.toNat))
  let rr := v .r-alpha*v .ap
  match field with
  | .x => v .x+alpha*v .p
  | .r => rr
  | .z => rr/decode (if read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)=0 then
      read64 memory (a.slot .diagonal i) else PreconditionUpdate.one)
  | _ => v field

theorem Arena.replay
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (admitted : Visibility.GlobalThreadSources words source) (thread : Fin n) :
    Flow.Runs (a.context thread) a.program (a.start memory (regs thread)) (t thread) := by
  apply Flow.Observed.replay_temporal (initial:=fun space => match space with | .global => memory | .shared => fun _ => 0)
    (Flow.Parallel.project run thread) entry_linear
  · intro access member read
    have member := Flow.Parallel.word_member.mp member
    obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp member
    have global := (a.parallel_access run member).1
    simpa only [global] using a.read_value run compatible admitted found read
  · intro access member
    obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp (Flow.Parallel.index_member.mp member)
    exact a.index_value run indexCompatible found
  · intro w stored store r readmem read same before
    exact a.future_apart run (Flow.Parallel.word_member.mp stored) store (Flow.Parallel.word_member.mp readmem) read before
  · intro w stored store global r readmem
    exact a.index_apart run (Flow.Parallel.word_member.mp stored) store (Flow.Parallel.index_member.mp readmem)
  · exact ⟨by intros; rfl,by intros; rfl⟩

theorem Arena.publication
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (field : Field) (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot field thread)=read64 (t thread).core.global (a.slot field thread) := by
  apply Flow.Parallel.publication_word run rfl
  intro owner access member different global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  obtain ⟨f,_,_,address⟩ := write.2
  rw [address]
  exact a.owners field f thread owner (Or.inr (Ne.symm different))

theorem Arena.local_value {regs : Registers}
    (run : Flow.Runs (a.context i) a.program (a.start memory regs) final) (done : final.halted=true)
    (field : Field) (output : field=.x ∨ field=.r ∨ field=.z) :
    decode (read64 final.core.global (a.slot field i))=a.value memory field i := by
  have result := entry_correct run rfl rfl done (a.live i) (a.local_valid memory regs i) (a.local_separate memory regs i)
  simp only [xValue,rValue,zValue,vectorValue,alphaValue,PreconditionUpdate.divisor,Assembly.maskFlag,
    a.setup_address,a.setup_boundary] at result
  change _ ∧ _ ∧ _ ∧ _ at result
  have scalar : ((Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core.regs 0+a.alpha).toNat=
      a.base.toNat+a.alpha.toNat := a.scalar_address
  simp only [scalar] at result
  rcases output with rfl|rfl|rfl
  · exact result.1
  · exact result.2.1
  · exact result.2.2.1

/-- Every completed admitted interleaving publishes the initial-input x, r and
z formulas. All read values follow from the same actual history's sources. -/
theorem Arena.parallel_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (admitted : Visibility.GlobalThreadSources words source) (done : ∀ i, (t i).halted=true)
    (field : Field) (output : field=.x ∨ field=.r ∨ field=.z) (thread : Fin n) :
    decode (read64 (GlobalPublication.publish memory words) (a.slot field thread))=a.value memory field thread := by
  rw [a.publication run field thread]
  exact a.local_value (a.replay run compatible indexCompatible admitted thread) (done thread) field output

theorem Arena.publication_outside {byte : Nat}
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (outside : ∀ f, f=Field.x ∨ f=Field.r ∨ f=Field.z →
      byte<a.base.toNat+(a.vector f).toNat ∨ a.base.toNat+(a.vector f).toNat+n*8≤byte) :
    GlobalPublication.publish memory words byte=memory byte := by
  apply GlobalPublication.outside
  intro owner access member global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  obtain ⟨f,kind,_,address⟩ := write.2
  rw [address]
  have bounds := outside f kind
  unfold Arena.slot
  have := owner.isLt; omega

end PtxTorchLean.Poisson.PTX.UpdateXRZ

import PoissonPTX.ConcurrentLimits
import PoissonPTX.ReductionStageSources
import PoissonPTX.ReductionUpdate

/-! Control of the 256-lane shared reduction tree. Initial lane sums are inputs;
the strided global loop, native predicate/branch lowering and output epilogue
are not part of this fragment. Guards use Concurrent.Instr.skip. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

/-- Publication zero is the initial lane sum; the next eight overwrite it. -/
def site (stage : Fin 9) : Nat := 2+8*stage.val

def stage (k : Fin 8) : List Instr :=
  [.skip (256 / 2^(k.val+1)) (11+8*k.val)] ++
  (PTX.Reduction.Update.code (BitVec.ofNat 64 (8*(256 / 2^(k.val+1))))).map .data ++
  [.sync 0]

def program : List Instr :=
  (SharedStore.code 0 8).map .data ++ [.sync 0] ++ (List.finRange 8).flatMap stage

def limit (pc : Nat) : Nat :=
  if 4≤pc ∧ pc<68 ∧ 1≤(pc-4)%8 ∧ (pc-4)%8≤6 then
    256 / 2^((pc-4)/8+1)
  else 256

theorem length : program.length=68 := by decide +kernel

theorem sites : StrictMono site := by
  intro a b h
  change 2+8*a.val<2+8*b.val
  change a.val<b.val at h
  omega

/-- Finite syntactic certificate, checked by the kernel. No event or value
history is enumerated here. -/
theorem checked_boundaries : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data _) => decide (limit pc.val≤limit (pc.val+1))
    | some (.skip count target) => decide (count≤limit (pc.val+1) ∧ 256≤limit target)
    | some (.sync _) => decide (256≤limit (pc.val+1))
    | none => true)=true := by decide +kernel

theorem boundaries : Limits.Boundaries 256 program limit := by
  have check (pc : Nat) (i : Instr) (fetch : program[pc]?=some i) :=
    checked_boundaries ⟨pc, by have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  refine ⟨?_,?_,?_⟩
  · intro pc op fetch; have h := check pc _ fetch; simpa [fetch] using h
  · intro pc count target fetch; have h := check pc _ fetch; simpa [fetch] using h
  · intro pc resource fetch; have h := check pc _ fetch; simpa [fetch] using h

theorem checked_stores : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data (.store64 .shared _ _)) =>
      decide (∃ k : Fin 9, pc.val=site k ∧ limit pc.val=active k)
    | _ => true)=true := by decide +kernel

theorem checked_forward : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.skip _ target) => decide (pc.val<target)
    | _ => true)=true := by decide +kernel

theorem forward : Forward program := by
  intro pc count target fetch
  have h := checked_forward ⟨pc, by have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  simpa [fetch] using h

/-- Store positions and shrinking writer ranges follow from arbitrary actual
interleavings starting at the entry, independently of chosen read values. -/
theorem store_coverage {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (member : Event.data thread access∈events)
    (write : access.data.store=true) (shared : access.space=.shared) :
    ∃ k : Fin 9, access.data.pc=site k ∧ thread.val<active k := by
  have inv : Limits.Invariant limit start := by
    intro t; rw [entry]; exact t.isLt
  have live := Limits.access_active run aligned inv boundaries member
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  cases hd with
  | store =>
    cases shared
    have h := checked_stores ⟨_, by have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
    simp only [fetch,decide_eq_true_eq] at h
    obtain ⟨k,position,bound⟩ := h
    exact ⟨k,position,by simpa only [bound] using live⟩
  | load => cases write

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

import PoissonPTX.CellMiddleCorrespondence
import PoissonPTX.Kernel

/-! The final two contractions and their separate rounded addition. The input
bytes are a phase snapshot here; concurrent availability is a separate layer. -/
namespace PtxTorchLean.Poisson.PTX.CellFinal
open Contraction

def left (width : Nat) (plane : Nat) : Matrix :=
  ⟨.shared,BitVec.ofNat 64 (plane*width*width*8),.row,.inner⟩
def right (offset : Word) : Matrix := ⟨.global,offset,.inner,.column⟩

def arithmetic (width : Nat) (b d : Word) : List Op :=
  Contraction.program width 8 (left width 5) (right d) ++
  Contraction.program width 9 (left width 6) (right b) ++
  [.fp .add 11 (.reg 8) (.reg 9)]

def fold (s : State) (width : Nat) (a b : Matrix) : Float :=
  (List.range width).foldl (fun z k => z+value s width k a*value s width k b) 0

def result (s : State) (width : Nat) (b d : Word) : Float :=
  fold s width (left width 5) (right d)+fold s width (left width 6) (right b)

def Inputs (s : State) (width : Nat) (b d : Word) : Prop :=
  ∀ k<width, (Valid s width k (left width 5) ∧ Valid s width k (right d)) ∧
    (Valid s width k (left width 6) ∧ Valid s width k (right b))

theorem inputs_stable (frame : Stable s t) : Inputs t width b d ↔ Inputs s width b d := by
  simp only [Inputs,stable_valid frame]

theorem contraction_keeps (h : Block (Contraction.program width acc a b) s t)
    (h1 : r≠1) (h2 : r≠2) (h13 : r≠13) (h4 : r≠4) (h5 : r≠5) (h10 : r≠10) (ha : r≠acc) :
    t.regs r=s.regs r := by
  apply SharedStore.block_keeps h
  simp only [Contraction.program,terms,List.forall_mem_cons,List.forall_mem_flatMap]
  constructor
  · simpa [SharedStore.keeps] using ha
  · intro k hk
    cases hs : a.space <;> cases ht : b.space <;>
      simp [term,Contraction.loadCode,indexCode,mac,hs,ht,SharedStore.keeps,h1,h2,h13,h4,h5,h10,ha]

theorem fold_stable (frame : Stable s t) : fold t width a b=fold s width a b := by
  simp only [fold,stable_value frame]

/-- A completed body determines the actual result register and preserves the
input memories, allocation bounds, coordinate/base registers and launch indices. -/
theorem arithmetic_correct (valid : Inputs s width b d)
    (run : Block (arithmetic width b d) s t) :
    decode (t.regs 11)=result s width b d ∧ Stable s t ∧
    t.regs 14=s.regs 14 ∧ t.regs 15=s.regs 15 := by
  obtain ⟨u,hx,rest⟩ := block_split (Contraction.program width 8 (left width 5) (right d))
    (Contraction.program width 9 (left width 6) (right b)++[.fp .add 11 (.reg 8) (.reg 9)])
    (by simpa [arithmetic,List.append_assoc] using run)
  obtain ⟨v,hy,last⟩ := block_split _ _ rest
  obtain ⟨x,fx⟩ := Contraction.correct (Or.inl rfl) (fun k hk => (valid k hk).1) hx
  obtain ⟨y,fy⟩ := Contraction.correct (Or.inr rfl)
    (fun k hk => ((inputs_stable fx).mpr valid k hk).2) hy
  have kept := contraction_keeps hy (r:=8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change decode (u.regs 8)=fold s width (left width 5) (right d) at x
  change decode (v.regs 9)=fold u width (left width 6) (right b) at y
  rw [fold_stable fx] at y
  have indices (r : Nat) (hr : r=14 ∨ r=15) : v.regs r=s.regs r := by
    exact (contraction_keeps (r:=r) hy (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (contraction_keeps (r:=r) hx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  cases last with | cons he tail =>
    cases he with | fp allowed =>
      cases tail
      refine ⟨?_,stable_trans (stable_trans fx fy) (stable_assign _ _ _ (by decide) (by decide) (by decide) (by decide)),?_,?_⟩
      · simpa [FP.Result,FP.apply,Operand.eval,assign,result,kept,x,y] using allowed
      · simpa [assign,advance] using indices 14 (Or.inl rfl)
      · simpa [assign,advance] using indices 15 (Or.inr rfl)

theorem arithmetic_exists (s : State) (valid : Inputs s width b d) :
    ∃ t, Block (arithmetic width b d) s t := by
  obtain ⟨u,hx⟩ := Contraction.exists_execution s (Or.inl rfl) (fun k hk => (valid k hk).1)
  have fx := (Contraction.correct (Or.inl rfl) (fun k hk => (valid k hk).1) hx).2
  obtain ⟨v,hy⟩ := Contraction.exists_execution u (Or.inr rfl)
    (fun k hk => ((inputs_stable fx).mpr valid k hk).2)
  obtain ⟨word,hw⟩ := FP.result_exists .add (v.regs 8) (v.regs 9)
  exact ⟨assign v 11 word,block_append (block_append hx hy) (.cons (.fp hw) .nil)⟩

end PtxTorchLean.Poisson.PTX.CellFinal

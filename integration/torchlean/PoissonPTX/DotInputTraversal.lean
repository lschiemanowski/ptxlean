import PoissonPTX.DotInputBody
import PoissonPTX.ControlFlowOperandWindow
import PoissonPTX.IndexedScalar

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- Exactly the indices visited by one lane. The list stops at the array end;
the proof below connects it to actual unsigned control and iteration steps. -/
def indices (count first : Nat) : List Nat :=
  if first<count then first::indices count (first+256) else []
termination_by count-first
decreasing_by omega

def atCursor (s : State) (index : Nat) : State :=
  {s with regs:=Function.update s.regs 12 (BitVec.ofNat 64 index)}

def contribution (s : State) (left right : Word) (index : Nat) : Float :=
  product (atCursor s index) left right

theorem stable_refl (s : State) : Stable s s := by repeat' constructor

theorem stable_trans (first : Stable a b) (second : Stable b c) : Stable a c := by
  rcases first with ⟨a,b,c,d,e,f,g,h,i⟩
  rcases second with ⟨j,k,l,m,n,o,p,q,r⟩
  exact ⟨j.trans a,k.trans b,l.trans c,m.trans d,n.trans e,o.trans f,p.trans g,q.trans h,r.trans i⟩

theorem valid_at (frame : Stable initial s)
    (valid : Valid (atCursor initial (cursor s)) left right) : Valid s left right := by
  rcases frame with ⟨mem,shared,base,bytes,sharedBase,sharedBytes,arena,lane,thread⟩
  simpa [Valid,atCursor,cursor,address,wide,Kernel.u32,BitVec.toNat_setWidth,mem,base,bytes,arena] using valid

theorem product_at (frame : Stable initial s) :
    product s left right=contribution initial left right (cursor s) := by
  rcases frame with ⟨mem,shared,base,bytes,sharedBase,sharedBytes,arena,lane,thread⟩
  simp [product,contribution,atCursor,cursor,address,wide,Kernel.u32,BitVec.toNat_setWidth,mem,arena]

theorem test (bounded : count<2^30) :
    Flow.OperandWindow.exhausted 12 (.imm (BitVec.ofNat 64 count)) s=decide (count≤cursor s) := by
  have small : count<4294967296 := by omega
  simp [Flow.OperandWindow.exhausted,Flow.Compare.apply,Operand.eval,cursor,Kernel.u32,
    BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

/-- Every completed traversal computes the separately rounded ordered fold.
The iteration count and values come from the actual blocks, not hypotheses. -/
theorem traversal_correct
    (actual : Flow.OperandWindow.Traversal origin 12 (.imm (BitVec.ofNat 64 count))
      ((body left right).map Indexed.Instr.data) s t)
    (bounded : count<2^30) (frame : Stable initial s)
    (safe : ∀ index<count, Valid (atCursor initial index) left right) :
    decode (t.regs 8)=(indices count (cursor s)).foldl
      (fun acc index => acc+contribution initial left right index) (decode (s.regs 8)) ∧
    Stable initial t := by
  induction actual with
  | @done s exhausted =>
    have after : count≤cursor s := by simpa only [test bounded,decide_eq_true_eq] using exhausted
    have stop : ¬cursor s<count := by omega
    rw [indices,ite_eq_right stop]
    exact ⟨rfl,frame⟩
  | @more s middle final inside block rest ih =>
    have before : cursor s<count := by
      have h : ¬count≤cursor s := by simpa only [test bounded,decide_eq_false_iff_not] using inside
      omega
    have valid : Valid {s with pc:=origin+2} left right := valid_at frame (safe _ before)
    obtain ⟨answer,increment,kept⟩ := correct (Indexed.underlying_block block) valid
    have incremented : cursor middle=cursor s+256 := progress before bounded increment
    have nextFrame : Stable initial {middle with pc:=origin} := stable_trans frame kept
    obtain ⟨result,finalFrame⟩ := ih nextFrame
    refine ⟨?_,finalFrame⟩
    rw [indices,ite_eq_left before,List.foldl_cons]
    rw [result]
    change (indices count (cursor middle)).foldl _ (decode (middle.regs 8))=_
    rw [incremented,answer]
    change (indices count (cursor s+256)).foldl _ (decode (s.regs 8)+product s left right)=_
    rw [product_at frame]

end PtxTorchLean.Poisson.PTX.DotInput

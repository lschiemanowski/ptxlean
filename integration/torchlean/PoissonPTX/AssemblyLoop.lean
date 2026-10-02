import PoissonPTX.AssemblyLookup
import PoissonPTX.ControlFlowLoop

namespace PtxTorchLean.Poisson.PTX.Assembly

def cursor (s : State) : Nat := (Kernel.u32 (s.regs 19)).toNat
def limit (s : State) : Nat := (Kernel.u32 (s.regs 20)).toNat
def atCursor (s : State) (k : Nat) : State := {s with regs:=Function.update s.regs 19 (BitVec.ofNat 64 k)}
def contribution (s : State) (entries element : Word) (k : Nat) : Float := decode (value (atCursor s k) entries element)

theorem stable_refl (s : State) : Stable s s := by repeat' constructor
theorem stable_trans (first : Stable s t) (second : Stable t u) : Stable s u := by
  rcases first with ⟨a,b,c,d,e,f,g,h⟩
  rcases second with ⟨i,j,k,l,m,n,o,p⟩
  exact ⟨i.trans a,j.trans b,k.trans c,l.trans d,m.trans e,n.trans f,o.trans g,p.trans h⟩

theorem stable_limit (frame : Stable s t) : limit t=limit s := by simp only [limit,frame.2.2.2.2.2.2.2]

theorem valid_at (frame : Stable initial s)
    (safe : Valid (atCursor initial (cursor s)) entries element) : Valid s entries element := by
  rcases frame with ⟨mem,shared,base,bytes,sharedBase,sharedBytes,arena,stop⟩
  simpa [Valid,indexAddress,valueAddress,index,atCursor,cursor,Kernel.u32,address32,address64,mem,base,bytes,arena] using safe

theorem value_at (frame : Stable initial s) :
    decode (value s entries element)=contribution initial entries element (cursor s) := by
  rcases frame with ⟨mem,shared,base,bytes,sharedBase,sharedBytes,arena,stop⟩
  simp [contribution,value,indexAddress,valueAddress,index,atCursor,cursor,Kernel.u32,address32,address64,mem,arena]

theorem cursor_increment (inside : cursor s<limit s) (updated : t.regs 19=add32 (s.regs 19) 1) :
    cursor t=cursor s+1 := by
  have bound : limit s<2^32 := (Kernel.u32 (s.regs 20)).isLt
  have small : cursor s+1<2^32 := by omega
  simpa [cursor,updated,Kernel.u32,add32,BitVec.toNat_add,BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (by decide : 4294967296 ∣ 18446744073709551616)] using Nat.mod_eq_of_lt small

/-- A loop execution performs exactly the ordered left fold over its initial
cursor range. Access validity is required for the initial arrays, not for
assumed loaded values or for a supplied loop result. -/
theorem traversal_correct (run : Flow.Loop.Traversal 19 20 (body entries element) s t)
    (frame : Stable initial s) (within : cursor s≤limit initial)
    (safe : ∀ k<limit initial, Valid (atCursor initial k) entries element) :
    decode (t.regs 8)=(List.range' (cursor s) (limit initial-cursor s)).foldl
      (fun acc k => acc+contribution initial entries element k) (decode (s.regs 8)) ∧ Stable initial t := by
  induction run with
  | @done s exhausted =>
    have done : limit s≤cursor s := by simpa [Flow.Loop.exhausted,Flow.Compare.apply,cursor,limit] using exhausted
    have same : cursor s=limit initial := by rw [stable_limit frame] at done; omega
    constructor
    · simp [same]
    · exact frame
  | @more s middle final inside block rest ih =>
    have before : cursor s<limit s := by simpa [Flow.Loop.exhausted,Flow.Compare.apply,cursor,limit] using inside
    have beforeInitial : cursor s<limit initial := by rw [stable_limit frame] at before; exact before
    have blockValid : Valid {s with pc:=2} entries element := valid_at frame (safe _ beforeInitial)
    obtain ⟨answer,increment,kept⟩ := body_correct block blockValid
    change decode (middle.regs 8)=decode (s.regs 8)+decode (value s entries element) at answer
    have changeCursor : cursor middle=cursor s+1 := cursor_increment before increment
    have nextFrame : Stable initial {middle with pc:=0} := stable_trans frame kept
    have nextBound : cursor {middle with pc:=0}≤limit initial := by change cursor middle≤limit initial; omega
    have result := ih nextFrame nextBound
    refine ⟨?_,result.2⟩
    have length : limit initial-cursor s=(limit initial-(cursor s+1))+1 := by omega
    rw [length,List.range'_succ,List.foldl_cons]
    change decode (final.regs 8)=_
    rw [result.1]
    change (List.range' (cursor middle) (limit initial-cursor middle)).foldl _ (decode (middle.regs 8))=_
    rw [changeCursor,answer,value_at frame]

theorem fetched_correct
    (run : Flow.Runs ctx (Flow.Loop.program 19 20 (body entries element)) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (within : cursor s.core≤limit s.core)
    (safe : ∀ k<limit s.core, Valid (atCursor s.core k) entries element) :
    decode (t.core.regs 8)=(List.range' (cursor s.core) (limit s.core-cursor s.core)).foldl
      (fun acc k => acc+contribution s.core entries element k) (decode (s.core.regs 8)) :=
  (traversal_correct (Flow.Loop.traversal run pc running done) (stable_refl _) within safe).1

end PtxTorchLean.Poisson.PTX.Assembly

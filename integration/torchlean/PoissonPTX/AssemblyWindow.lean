import PoissonPTX.AssemblyLoop
import PoissonPTX.ControlFlowWindow

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- The same ordered fold at native instruction counters and the real exit. -/
theorem window_correct (run : Flow.Window.Traversal origin 19 20 (body entries element) s t)
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
    have blockValid : Valid {s with pc:=origin+2} entries element := valid_at frame (safe _ beforeInitial)
    obtain ⟨answer,increment,kept⟩ := body_correct block blockValid
    change decode (middle.regs 8)=decode (s.regs 8)+decode (value s entries element) at answer
    have changeCursor : cursor middle=cursor s+1 := cursor_increment before increment
    have nextFrame : Stable initial {middle with pc:=origin} := stable_trans frame kept
    have nextBound : cursor {middle with pc:=origin}≤limit initial := by change cursor middle≤limit initial; omega
    have result := ih nextFrame nextBound
    refine ⟨?_,result.2⟩
    have length : limit initial-cursor s=(limit initial-(cursor s+1))+1 := by omega
    rw [length,List.range'_succ,List.foldl_cons]
    change decode (final.regs 8)=_
    rw [result.1]
    change (List.range' (cursor middle) (limit initial-cursor middle)).foldl _ (decode (middle.regs 8))=_
    rw [changeCursor,answer,value_at frame]

end PtxTorchLean.Poisson.PTX.Assembly

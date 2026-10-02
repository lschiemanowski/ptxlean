import PoissonPTX.RepeatedSharedChecks

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks

def separate : List (Event 2) := [
  .data 0 ⟨.shared,⟨0,true,0,7⟩⟩,.data 1 ⟨.shared,⟨0,false,0,7⟩⟩]

theorem no_edge (a b : Nat) : ¬Edge separate a b := by
  intro edge
  rcases edge with ⟨thread,left,right,ha,hb,lt⟩ | ⟨writer,reader,wa,ra,key,x,y,hw,hr,hx,hy,one,two,three⟩
  · have aBound : a<2 := (List.getElem?_eq_some_iff.mp ha).1
    have bBound : b<2 := (List.getElem?_eq_some_iff.mp hb).1
    interval_cases a <;> interval_cases b <;> simp [separate] at ha hb <;> simp_all
    exact (by decide : (0 : Fin 2)≠1) (ha.1.trans hb.1.symm)
  · have member := List.mem_of_getElem? hy
    simp [separate] at member

/-- Mere order in a chronological interleaving does not synchronize threads. -/
theorem chronological_is_not_causal : ¬Before separate 0 1 := by
  intro path
  exact Ptx.Path.contained (s:=fun _ _ => False) (fun a b h => no_edge a b h)
    (fun _ _ _ h _ => h) path

def program : List Instr := [.skip 1 2,.data (.store64 .shared (.imm 0) (.imm 7)),.sync 0,
  .data (.load64 .shared 0 (.imm 0))]
def start : Concurrent.State 2 := ⟨fun _ =>
  ⟨0,fun _ => 0,fun _ => 0,fun _ => 0,0,0,0,8⟩,Ptx.Barrier.reset 0,none⟩
def cfg : Config 2 := ⟨0,by decide⟩
def execution (value : Word) := execute cfg program (fun _ _ => value) [0,0,1,0,1,0,1] start
def result (value : Word) : Outcome 2 := (execution value).getD ⟨start,[]⟩
def history (value : Word) : List (Event 2) := [
  .data 0 ⟨.shared,⟨1,true,0,7⟩⟩,
  .barrier (.arrival ⟨0,0,0,2⟩ 0),.barrier (.arrival ⟨0,0,0,2⟩ 1),
  .barrier (.completion ⟨0,0,0,2⟩),
  .data 0 ⟨.shared,⟨3,false,0,value⟩⟩,.data 1 ⟨.shared,⟨3,false,0,value⟩⟩]

theorem executed (value : Word) : execution value=some (result value) ∧ (result value).events=history value := by
  constructor <;> rfl

theorem actual (value : Word) : Runs cfg program start (history value) (result value).state := by
  have run := execute_sound (executed value).1
  simpa only [(executed value).2] using run

/-- Actual arrival and completion records supply the cross-thread edge. -/
theorem synchronized (value : Word) : Before (history value) 0 5 :=
  .edge (.inr ⟨0,1,⟨.shared,⟨1,true,0,7⟩⟩,⟨.shared,⟨3,false,0,value⟩⟩,
    ⟨0,0,0,2⟩,1,3,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩)

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks

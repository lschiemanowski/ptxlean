import PoissonPTX.CellEntryExec
import PoissonPTX.CellEntryLaunch

namespace PtxTorchLean.Poisson.PTX.CellEntry.Checks
open Ptx
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def memory : Memory :=
  write64 (write64 (write64 (write64
    (write32 (write32 (write32 (write32 (fun _ => 0) 4112 3) 4116 1) 4120 0) 4124 2)
    4160 0x3ff0000000000000) 4168 0x8000000000000000) 4176 0x7ff8000000000042) 4184 0xc000000000000000

def seed : PTX.State := {
  pc:=0, regs:=fun _ => 0xaaaaaaaaaaaaaaaa, global:=memory, shared:=fun _ => 0x5a,
  globalStart:=4096, globalBytes:=512, sharedStart:=256, sharedBytes:=224 }

def start : State 32 := ⟨⟨fun _ => seed,Barrier.reset 0,none⟩,fun _ => true⟩
def cfg : Concurrent.Config 32 := ⟨1,by decide⟩
def bases : Space → Word | .global => 4096 | .shared => 256
def ctx := CellPrologue.threadContext bases 1
def kernel := program 2 0 64
def choose (_ : Fin 32) (s : PTX.State) : Word :=
  if s.pc=12 then (read32 s.global (s.regs 2).toNat).setWidth 64
  else read64 s.global (s.regs 2).toNat

/-- Padding lanes execute setup and the branch, then join the same barrier. -/
def schedule : List (Fin 32) :=
  (List.finRange 32).flatMap (fun t => List.replicate (if t.val<4 then 20 else 8) t) ++ List.finRange 32
def candidate := execute cfg ctx kernel choose schedule start
def result : Outcome 32 := candidate.getD ⟨start,[],[]⟩

theorem executed : candidate=some result := by
  have success : candidate.isSome=true := by decide +kernel
  cases he : candidate with
  | none => simp [he] at success
  | some out => simp [result,he]

theorem actual_run : Runs cfg ctx kernel start result.events result.indices result.state := execute_sound executed

theorem completed : (∀ t : Fin 32, (result.state.core.lanes t).pc=21) ∧
    result.state.core.barrier.generation=1 ∧ result.state.core.site=none ∧
    result.indices.length=4 ∧ result.events.length=41 := by decide +kernel

theorem gathered :
    read64 (result.state.core.lanes 0).shared 256=0xc000000000000000 ∧
    read64 (result.state.core.lanes 1).shared 264=0x8000000000000000 ∧
    read64 (result.state.core.lanes 2).shared 272=0x3ff0000000000000 ∧
    read64 (result.state.core.lanes 3).shared 280=0x7ff8000000000042 := by decide +kernel

theorem padding_untouched : ∀ t : Fin 28,
    (result.state.core.lanes ⟨t.val+4,by omega⟩).shared 256=0x5a := by decide +kernel

theorem no_early_release :
    (execute cfg ctx kernel choose (schedule.take (schedule.length-1)) start).map
      (fun out => (out.state.core.barrier.generation,(out.state.core.lanes 0).pc))=some (0,20) := by decide +kernel

theorem unsigned_index_overlap :
    ¬IndexSources.ReadOnly ([.data 0 ⟨.global,⟨0,true,0,0⟩⟩] : List (Concurrent.Event 32)) 4 := by
  intro h
  have bad := h 0 0 ⟨.global,⟨0,true,0,0⟩⟩ rfl rfl rfl 4 0
  exact bad rfl


def initial : Space → Memory
  | .global => memory
  | .shared => fun _ => 0x5a

def wordsInitial (events : List (Concurrent.Event 32)) : Bool := events.all fun e =>
  match e with
  | .data _ a => if a.data.store then true else
      decide (∀ k : Fin 8, byte a.data.value k.val=initial a.space (a.data.address+k.val))
  | .barrier _ => true

def indicesInitial (indices : List (Fin 32 × IndexSources.Access)) : Bool := indices.all fun (_,a) =>
  decide (∀ k : Fin 4, IndexSources.byte32 a.value k.val=memory (a.address+k.val))

theorem sources_checked : wordsInitial result.events=true ∧ indicesInitial result.indices=true := by decide +kernel

theorem compatible : Concurrent.Visibility.Compatible initial result.events (fun _ _ => .initial) := by
  intro r reader a observed read k
  have member := List.mem_of_getElem? observed
  have checked := List.all_eq_true.mp sources_checked.1 (.data reader a) member
  simp only [read,Bool.false_eq_true,↓reduceIte,decide_eq_true_eq] at checked
  exact checked k

theorem index_compatible : IndexSources.Compatible memory result.events result.indices (fun _ _ => .initial) := by
  intro r reader a observed k
  have member := List.mem_of_getElem? observed
  have checked := List.all_eq_true.mp sources_checked.2 (reader,a) member
  simp only [decide_eq_true_eq] at checked
  exact checked k

theorem wrong_index_rejected : indicesInitial [(0,⟨12,4112,0⟩)]=false := by decide +kernel


theorem launch_from_execution :
    Nonempty (Concurrent.CellMiddle.Numeric.Launch 2 bases (resume result.state)) := by
  apply arithmetic_launch actual_run (thread:=0) (memory:=initial) (chosen:=fun _ _ => .initial)
    (selected:=fun _ _ => .initial)
  · intro thread waiting
    simp [start,Barrier.reset] at waiting
  · intro thread; rfl
  · exact compatible
  · exact index_compatible
  · intro thread; rfl
  · exact (by have h := completed.1 (0 : Fin 32); omega)
  · decide
  · decide
  · decide
  · unfold CellGather.Valid; decide +kernel

end PtxTorchLean.Poisson.PTX.CellEntry.Checks

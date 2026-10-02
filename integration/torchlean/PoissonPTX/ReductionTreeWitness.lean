import PoissonPTX.ReductionUpdate
import PoissonPTX.ReductionSources
import PoissonPTX.ConcurrentExec

/-! A four-lane, two-stage fetched regression using the real pair-update body.
The guard is Concurrent.skip (combined lane test and branch), not a proof of
the emitted entry's predicate instructions or its strided input loop. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev one : Word := 0x3ff0000000000000
abbrev two : Word := 0x4000000000000000
abbrev three : Word := 0x4008000000000000
abbrev four : Word := 0x4010000000000000
abbrev six : Word := 0x4018000000000000

def program : List Instr :=
  (SharedStore.code 0 8).map Instr.data ++ [.sync 0,.skip 2 11] ++
  (PTX.Reduction.Update.code 16).map Instr.data ++ [.sync 0,.skip 1 19] ++
  (PTX.Reduction.Update.code 8).map Instr.data ++ [.sync 0]

def input (t : Fin 4) : Word := [one,two,three,four][t.val]'(by simp)

def start : Concurrent.State 4 := ⟨fun t =>
  ⟨0,fun r => if r=14 then BitVec.ofNat 64 t.val else if r=8 then input t else 0,
    fun _ => 0,fun _ => 0,0,0,0,32⟩,Ptx.Barrier.reset 0,none⟩
def cfg : Config 4 := ⟨0,by decide⟩

def choose (left right : Word) (thread : Fin 4) (pc : Nat) : Word :=
  if pc=7 then input thread else if pc=8 then (if thread=0 then three else four)
  else if pc=15 then left else right

def schedule : List (Fin 4) :=
  [0,0,0,1,1,1,2,2,2,3,3,3,0,1,2,3] ++
  [0,0,0,0,0,0,0,1,1,1,1,1,1,1,2,3,0,1,2,3] ++
  [0,0,0,0,0,0,0,1,2,3,0,1,2,3]

def execution (left right : Word) := execute cfg program (choose left right) schedule start
def result (left right : Word) : Outcome 4 := (execution left right).getD ⟨start,[]⟩
def sum (left right : Word) := encode (decode left + decode right)

def fence (generation site : Nat) : List (Event 4) :=
  [.barrier (.arrival ⟨0,0,generation,site⟩ 0),.barrier (.arrival ⟨0,0,generation,site⟩ 1),
   .barrier (.arrival ⟨0,0,generation,site⟩ 2),.barrier (.arrival ⟨0,0,generation,site⟩ 3),
   .barrier (.completion ⟨0,0,generation,site⟩)]

def history (left right : Word) : List (Event 4) :=
  [.data 0 ⟨.shared,⟨2,true,0,one⟩⟩,.data 1 ⟨.shared,⟨2,true,8,two⟩⟩,
   .data 2 ⟨.shared,⟨2,true,16,three⟩⟩,.data 3 ⟨.shared,⟨2,true,24,four⟩⟩] ++ fence 0 3 ++
  [.data 0 ⟨.shared,⟨7,false,0,one⟩⟩,.data 0 ⟨.shared,⟨8,false,16,three⟩⟩,
   .data 0 ⟨.shared,⟨10,true,0,four⟩⟩,
   .data 1 ⟨.shared,⟨7,false,8,two⟩⟩,.data 1 ⟨.shared,⟨8,false,24,four⟩⟩,
   .data 1 ⟨.shared,⟨10,true,8,six⟩⟩] ++ fence 1 11 ++
  [.data 0 ⟨.shared,⟨15,false,0,left⟩⟩,.data 0 ⟨.shared,⟨16,false,8,right⟩⟩,
   .data 0 ⟨.shared,⟨18,true,0,sum left right⟩⟩] ++ fence 2 19

/-- A checked successful concrete run with the final pair four and six. -/
theorem recorded : (execution four six).map Outcome.events=some (history four six) := by
  decide +kernel

theorem executed : execution four six=some (result four six) ∧
    (result four six).events=history four six := by
  have h := recorded
  cases eq : execution four six with
  | none => rw [eq] at h; cases h
  | some out =>
    rw [eq] at h
    have recorded := Option.some.inj h
    constructor
    · simp only [result,eq,Option.getD_some]
    · simpa only [result,eq,Option.getD_some] using recorded

theorem actual : Runs cfg program start (history four six) (result four six).state := by
  have run := execute_sound executed.1
  simpa only [executed.2] using run

/-- Every lane reaches the end of this barrier-terminated fragment. -/
theorem completed : ∀ t : Fin 4, ((result four six).state.lanes t).pc = program.length := by
  decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness

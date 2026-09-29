import PoissonPTX.ConcurrentExec
import PoissonPTX.BarrierSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Checks
open Ptx
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def cfg : Config 2 := ⟨0,by decide⟩

def seed (i : Fin 2) : PTX.State := {
  pc := 0, regs := fun r => if r=14 then BitVec.ofNat 64 i.val else if r=8 then 42 else 0,
  global := fun _ => 0, shared := fun _ => 0,
  globalStart := 0, globalBytes := 0, sharedStart := 0, sharedBytes := 8 }

def start : State 2 := ⟨seed,Barrier.reset 0,none⟩

/-- Lane zero writes; lane one skips the store but must still arrive. Both then
read the word and synchronize again at a different site of resource zero. -/
def program : List Instr :=
  [.skip 1 4] ++ (SharedStore.code 0 8).map Instr.data ++
  [.sync 0,.data (.load64 .shared 4 (.imm 0)),.sync 0]

def schedule : List (Fin 2) := [0,0,0,0,1,0,1,0,1,0,1]

def result (word : Word) : Outcome 2 :=
  (execute cfg program (fun _ _ => word) schedule start).getD ⟨start,[]⟩

theorem successful (word : Word) : (execute cfg program (fun _ _ => word) schedule start).isSome=true := by
  rfl

theorem executed (word : Word) :
    execute cfg program (fun _ _ => word) schedule start=some (result word) := by
  have h := successful word
  cases he : execute cfg program (fun _ _ => word) schedule start with
  | none => simp [he] at h
  | some out => simp [result,he]

theorem actual_run (word : Word) : Runs cfg program start (result word).events (result word).state :=
  execute_sound (executed word)

def history (word : Word) : List (Event 2) :=
  [.data 0 ⟨.shared,⟨3,true,0,42⟩⟩,
   .barrier (.arrival ⟨0,0,0,4⟩ 0),.barrier (.arrival ⟨0,0,0,4⟩ 1),
   .barrier (.completion ⟨0,0,0,4⟩),
   .data 0 ⟨.shared,⟨5,false,0,word⟩⟩,.data 1 ⟨.shared,⟨5,false,0,word⟩⟩,
   .barrier (.arrival ⟨0,0,1,6⟩ 0),.barrier (.arrival ⟨0,0,1,6⟩ 1),
   .barrier (.completion ⟨0,0,1,6⟩)]

theorem event_history (word : Word) : (result word).events=history word := by
  rfl

theorem ordered (word : Word) : Visibility.Across (history word) 0 5 := by
  exact ⟨0,1,⟨.shared,⟨3,true,0,42⟩⟩,⟨.shared,⟨5,false,0,word⟩⟩,
    ⟨0,0,0,4⟩,1,3,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

/-- A candidate can execute with an old value: instruction execution alone
must not preclude it by pretending the memory is sequentially consistent. -/
theorem stale_candidate_exists : ∃ final, Runs cfg program start (history 0) final := by
  refine ⟨(result 0).state,?_⟩
  rw [← event_history]; exact actual_run 0

theorem stale_sources_rejected :
    ¬Visibility.Performed (history 0) (fun _ _ => .initial) := by
  intro h
  have impossible := h 0 5 0 1 ⟨.shared,⟨3,true,0,42⟩⟩ ⟨.shared,⟨5,false,0,0⟩⟩
    rfl rfl rfl rfl rfl rfl (ordered 0) 0 0 rfl
  exact impossible rfl

/-- There is no special exemption for an inactive lane at the barrier. -/
theorem inactive_missing : execute cfg program (fun _ _ => 42) [0,0,0,0,0,0] start=none := by
  decide +kernel

theorem reuse : (result 42).state.barrier.generation=2 ∧
    (∀ t, ((result 42).state.lanes t).pc=7) := by decide +kernel

def block32 : Config 32 := ⟨0,by decide⟩
def state32 : State 32 := ⟨fun _ => seed 0,Barrier.prefixState 0 30,some 0⟩

theorem last_padding_blocks :
    (Barrier.step (barrierConfig block32 state32 30) state32.barrier
      (barrierRequest block32 state32 30 0)).disposition≠.released := by decide +kernel

theorem fresh_compatible : Visibility.Compatible (fun _ _ => 0) (history 42)
    (fun _ k => .store 0 k) := by
  intro r reader ra hr read k
  have mem := List.mem_of_getElem? hr
  simp [history] at mem
  rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp at read
  all_goals exact ⟨0,⟨.shared,⟨3,true,0,42⟩⟩,rfl,rfl,rfl,rfl,rfl⟩

theorem fresh_performed : Visibility.Performed (history 42) (fun _ k => .store 0 k) := by
  simp [Visibility.Performed]

theorem stale_compatible : Visibility.Compatible (fun _ _ => 0) (history 0)
    (fun _ _ => .initial) := by
  intro r reader ra hr read k
  have mem := List.mem_of_getElem? hr
  simp [history] at mem
  rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp at read
  all_goals simp [byte]

theorem unique_writer (word : Word) : Visibility.SoleWriter (history word) 0 0 := by
  intro other thread access observed store space j k same
  have bound : other<9 := by
    by_contra h
    have hn : (history word)[other]?=none := List.getElem?_eq_none (by simpa [history] using Nat.le_of_not_gt h)
    rw [hn] at observed; contradiction
  interval_cases other <;> simp_all [history]
  all_goals obtain ⟨_,rfl⟩ := observed; contradiction

theorem actual_read_correct (word : Word) (source : Nat → Fin 8 → Sources.Origin Nat)
    (compatible : Visibility.Compatible (fun _ _ => 0) (result word).events source)
    (performed : Visibility.Performed (result word).events source) : word=42 := by
  rw [event_history] at compatible performed
  exact (Visibility.read_from_writer compatible performed
    (w:=0) (r:=5) (writer:=0) (reader:=1)
    (wa:=⟨.shared,⟨3,true,0,42⟩⟩) (ra:=⟨.shared,⟨5,false,0,word⟩⟩)
    rfl rfl rfl rfl rfl rfl rfl (ordered word) (unique_writer word)).1

def unsynchronized : List (Event 2) :=
  [.data 0 ⟨.shared,⟨3,true,0,42⟩⟩,.data 1 ⟨.shared,⟨5,false,0,0⟩⟩]

/-- Without a completed barrier the necessary constraints allow old bytes.
This is a constraint witness, not a full PTX-admission theorem. -/
theorem no_barrier_old_allowed :
    Visibility.Compatible (fun _ _ => 0) unsynchronized (fun _ _ => .initial) ∧
    Visibility.Performed unsynchronized (fun _ _ => .initial) := by
  constructor
  · intro r reader ra hr read k
    have mem := List.mem_of_getElem? hr
    simp [unsynchronized] at mem
    rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp at read
    · simp [byte]
  · intro w r writer reader wa ra hw hr sw sr ws rs ordered
    obtain ⟨wt,rt,wv,rv,key,a,c,_,_,ha,_⟩ := ordered
    have mem := List.mem_of_getElem? ha
    simp [unsynchronized] at mem

end PtxTorchLean.Poisson.PTX.Concurrent.Checks

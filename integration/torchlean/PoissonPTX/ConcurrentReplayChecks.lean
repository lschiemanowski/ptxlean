import PoissonPTX.ConcurrentComputedStore

/-! A nonzero, two-thread interleaving checks the projection and actual store
endpoint. This small fixture is not a whole-cell execution theorem. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks
open Ptx
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def two : Word := 0x4000000000000000
def three : Word := 0x4008000000000000
def six : Word := 0x4018000000000000
def memory : Space → Memory
  | .global => write64 (write64 (fun _ => 0) 0 two) 8 three
  | .shared => fun _ => 0
def a : Contraction.Matrix := ⟨.global,0,.inner,.inner⟩
def b : Contraction.Matrix := ⟨.global,8,.inner,.inner⟩
def ops : List Op := Contraction.program 1 8 a b ++ storePrefix
def kernel : List Instr := ops.map Instr.data ++ [.data (.store64 .shared (.reg 2) (.reg 8))]
def seed (thread : Fin 2) : PTX.State := {
  pc:=0,regs:=fun r => if r=14 then BitVec.ofNat 64 thread.val else 0,
  global:=fun _ => 0, shared:=fun _ => 0,
  globalStart:=0,globalBytes:=16,sharedStart:=0,sharedBytes:=16 }
def start : State 2 := ⟨seed,Barrier.reset 0,none⟩
def cfg : Config 2 := ⟨0,by decide⟩
def schedule : List (Fin 2) := (List.range ops.length).flatMap fun _ => [0,1]
def choose (_ : Fin 2) (pc : Nat) : Word := if pc=6 then two else three
def candidate := execute cfg kernel choose schedule start
def result : Outcome 2 := candidate.getD ⟨start,[]⟩

theorem executed : candidate=some result := by
  have h : candidate.isSome=true := by decide +kernel
  cases he : candidate with
  | none => simp [he] at h
  | some out => simp [result,he]

theorem actual_run : Runs cfg kernel start result.events result.state := execute_sound executed

def loadEvents : List (Event 2) :=
  [.data 0 ⟨.global,⟨6,false,0,two⟩⟩,.data 1 ⟨.global,⟨6,false,0,two⟩⟩,
   .data 0 ⟨.global,⟨12,false,8,three⟩⟩,.data 1 ⟨.global,⟨12,false,8,three⟩⟩]

theorem events_exact : result.events=loadEvents := by decide +kernel

theorem compatible : Visibility.Compatible memory result.events (fun _ _ => .initial) := by
  intro r reader ra observed read k
  rw [events_exact] at observed
  have mem := List.mem_of_getElem? observed
  simp only [loadEvents,List.mem_cons,List.not_mem_nil,or_false,Event.data.injEq] at mem
  rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals dsimp only
  all_goals fin_cases k <;> decide +kernel

theorem input_reads : Reads memory 0 0 ops.length result.events := by
  apply Visibility.readonly_reads compatible
  intro access member read lo hi w writer wa observed store space j k
  rw [events_exact] at observed
  have mem := List.mem_of_getElem? observed
  simp only [loadEvents,List.mem_cons,List.not_mem_nil,or_false,Event.data.injEq] at mem
  rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp at store

def stored : Outcome 2 := (tick cfg kernel choose 0 result.state).getD ⟨result.state,[]⟩
theorem actual_store : Step cfg kernel 0 result.state stored := by
  apply tick_sound
  have h : (tick cfg kernel choose 0 result.state).isSome=true := by decide +kernel
  cases he : tick cfg kernel choose 0 result.state with
  | none => simp [he] at h
  | some out => simp [stored,he]
def access : Access := ⟨.shared,⟨17,true,0,six⟩⟩
theorem store_record : stored.events=[.data 0 access] := by decide +kernel

theorem no_store_ops : ∀ p : Fin ops.length, noStore ops[p.val]=true := by decide +kernel

theorem stored_tensor : decode access.data.value=
    Spec.get2 (Spec.matMulSpec (Contraction.leftTensor (view memory (start.lanes 0)) 1 a)
      (Contraction.rightTensor (view memory (start.lanes 0)) 1 b)) 0 0 := by
  have forward : Forward kernel := by
    intro pc active target fetch
    have mem := List.mem_of_getElem? fetch
    simp [kernel,List.mem_map] at mem
  have slice : Slice kernel ops 0 ops.length := by
    intro pc lo hi
    have h := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
    refine ⟨ops[pc],?_,h,?_⟩
    · simp [kernel,List.getElem?_append,hi]
    · exact no_store_ops ⟨pc,hi⟩
  exact (stored_contraction actual_run (by simp [Aligned,start,Barrier.reset]) forward [] []
    (by simpa [ops] using slice) rfl (by decide +kernel)
    (by simpa [ops] using input_reads) (Or.inl rfl)
    (by
      intro k hk
      have eq : k=0 := by omega
      subst k
      unfold Contraction.Valid
      decide +kernel)
    actual_store (address:=.reg 2) (by decide +kernel)
    (by rw [store_record]; simp)).2.2

/-- An arbitrary wrong word is a candidate load but not a compatible read from
these read-only bytes. Replay cannot silently replace it with the right value. -/
theorem wrong_read_rejected :
    ¬Visibility.Compatible memory [Event.data (0 : Fin 2) ⟨.global,⟨6,false,0,three⟩⟩]
      (fun _ _ => .initial) := by
  intro compatible
  have h := compatible 0 0 _ rfl rfl (⟨6,by decide⟩ : Fin 8)
  change byte three 6=memory .global 6 at h
  revert h
  decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks

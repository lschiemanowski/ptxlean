import PoissonPTX.ObservedParallelReplay
import PoissonPTX.ObservedExists
import PoissonPTX.SourceCheck

namespace PtxTorchLean.Poisson.PTX.Flow.Observed.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def memory : Memory := write64 (write32 (fun _ => 0) 0 2) 8 0x3ff8000000000000

def start : State where
  core := {
    pc := 0
    regs := fun _ => 0
    global := memory
    shared := fun _ => 0
    globalStart := 0
    globalBytes := 32
    sharedStart := 0
    sharedBytes := 0 }
  predicates := fun _ => false
  halted := false
def ctx : Kernel.Context := ⟨0,0,0⟩
def code : List Instr := [.data (.load32 12 0),.data (.data (.load64 .global 4 (.imm 8))),
  .data (.data (.store64 .global (.imm 24) (.reg 4))),.ret]
def indexed : State := {start with core:=assign start.core 12 2}
def loaded : State := {indexed with core:=assign indexed.core 4 0x3ff8000000000000}
def stored : State := {loaded with core:=put loaded.core .global 24 0x3ff8000000000000}
def final : State := halt stored

def words : List Concurrent.Access := [⟨.global,⟨1,false,8,0x3ff8000000000000⟩⟩,
  ⟨.global,⟨2,true,24,0x3ff8000000000000⟩⟩]
def indices : List IndexSources.Access := [⟨0,0,2⟩]

theorem actual : Runs ctx code start words indices final := by
  apply Runs.cons (s:=start) (t:=indexed) (access:=none) (index:=some ⟨0,0,2⟩)
    ⟨rfl,_,rfl,.data (.load32 (s:=start.core) (addr:=0) (dst:=12) (word:=2) (by decide +kernel))⟩
  apply Runs.cons (s:=indexed) (t:=loaded) (access:=some ⟨.global,⟨1,false,8,0x3ff8000000000000⟩⟩) (index:=none)
    ⟨rfl,_,rfl,.data (.data (.load (s:=indexed.core) (sp:=.global) (addr:=.imm 8) (dst:=4) (word:=0x3ff8000000000000) (by decide +kernel)))⟩
  apply Runs.cons (s:=loaded) (t:=stored) (access:=some ⟨.global,⟨2,true,24,0x3ff8000000000000⟩⟩) (index:=none)
    ⟨rfl,_,rfl,.data (.data (.store (s:=loaded.core) (sp:=.global) (addr:=.imm 24) (src:=.reg 4) (by decide +kernel)))⟩
  apply Runs.cons (s:=stored) (t:=final) (access:=none) (index:=none)
    ⟨rfl,_,rfl,.simple (by intro op h; cases h)⟩
  exact .nil

theorem compatible : Concurrent.Visibility.Compatible start.core.memory (events words) (fun _ _ => .initial) :=
  Concurrent.SourceCheck.sound (by decide +kernel)

theorem index_compatible : IndexSources.Compatible memory (events words) (indexEvents indices) (fun _ _ => .initial) := by
  intro r reader ra observed k
  have bound := (List.getElem?_eq_some_iff.mp observed).1
  change r<1 at bound
  have zero : r=0 := by omega
  subst r
  change some ((0 : Fin 1),(⟨0,0,2⟩ : IndexSources.Access))=some (reader,ra) at observed
  cases observed
  fin_cases k <;> decide +kernel

theorem separated : Separate words indices := by
  constructor
  · intro w member store r memberR read same
    simp [words] at member memberR
    rcases member with rfl|rfl <;> rcases memberR with rfl|rfl <;> simp_all
  · intro w member store global r memberR
    simp [words] at member
    have same : r=⟨0,0,2⟩ := by simpa [indices] using memberR
    subst r
    rcases member with rfl|rfl <;> simp_all

theorem replayed : Flow.Runs ctx code start final := admitted_replay actual compatible index_compatible separated

theorem output : decode (read64 final.core.global 24)=1.5 := by decide +kernel

/-- Candidate instruction validity alone admits a forged load. The same byte
source check rejects it, preserving the distinction between the two layers. -/
theorem forged_rejected : ¬Concurrent.SourceCheck.Checked start.core.memory
    (events [⟨.global,⟨1,false,8,0x4000000000000000⟩⟩]) (fun _ _ => .initial) := by decide +kernel

end PtxTorchLean.Poisson.PTX.Flow.Observed.Checks

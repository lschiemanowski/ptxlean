import PoissonPTX.ParallelResidualLayout
import PoissonPTX.WeakPadding

namespace PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks
open Kernel Sources
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def arena : Arena 2 where
  base:=0
  rhs:=0
  ap:=16
  output:=32
  bytes:=48
  small:=by decide
  aligned:=by decide
  noWrap:=by decide
  fields:=by
    intro off h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> decide
  separated:=by
    intro off h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> decide

def memory : Memory :=
  write64 (write64 (write64 (write64 (fun _=>0) 0 0x4008000000000000)
    8 0x4014000000000000) 16 0x3ff0000000000000) 24 0x3ff0000000000000

def inputs : Inputs 2 := arena.inputs memory (fun _ _=>0)

theorem forward_order :
    (read64 (publish inputs (witness inputs) [0,1]) 32,
     read64 (publish inputs (witness inputs) [0,1]) 40) =
    (0x4000000000000000,0x4010000000000000) := by decide +kernel

theorem reverse_order :
    (read64 (publish inputs (witness inputs) [1,0]) 32,
     read64 (publish inputs (witness inputs) [1,0]) 40) =
    (0x4000000000000000,0x4010000000000000) := by decide +kernel

/-- The candidate interpreter genuinely permits an incorrect input observation
until source checking: four minus one produces three, instead of three minus one. -/
def badChoice (pc : Nat) : Word :=
  if pc=9 then 0x4010000000000000 else if pc=13 then 0x3ff0000000000000 else 0x4008000000000000

theorem bad_candidate_executes :
    ((execute (inputs.context 0) (Kernel.Residual.program 2 0 16 32) badChoice 20 (inputs.start 0)).map
      fun pair => pair.2.map Access.value) =
      some [0x4010000000000000,0x3ff0000000000000,0x4008000000000000] := by decide +kernel

def badEvents (e : Fin 3) : Access :=
  if e=0 then ⟨9,false,0,0x4010000000000000⟩ else
  if e=1 then ⟨13,false,16,0x3ff0000000000000⟩ else
    ⟨18,true,32,0x4008000000000000⟩

theorem bad_initial_source_rejected :
    ¬Compatible memory badEvents (fun _ _=>.initial) := by unfold Compatible; decide +kernel

theorem output_cannot_source_input :
    ¬Compatible memory badEvents (fun _ k=>.store 2 k) := by unfold Compatible; decide +kernel

/-- Adjacent bases are not enough: offsets less than eight overlap physically. -/
theorem overlapping_bytes : ¬Sources.Disjoint 32 36 := by unfold Sources.Disjoint; decide +kernel

theorem padding_has_no_access :
    ((execute ⟨0,2,0⟩ (Kernel.Residual.program 2 0 16 32) badChoice 20 (inputs.start 0)).map
      fun pair => (pair.1.halted,pair.2)) = some (true,[]) := by decide +kernel

/-- The source overapproximation really allows tearing when writers overlap;
it has not silently assumed whole-word atomicity for general weak accesses. -/
def tornEvents (e : Fin 3) : Access :=
  if e=0 then ⟨0,true,0,0x00000000ffffffff⟩ else
  if e=1 then ⟨0,true,0,0xffffffff00000000⟩ else
    ⟨1,false,0,0xffffffffffffffff⟩

def tornSource (_ : Fin 3) (k : Fin 8) : Origin (Fin 3) :=
  if k.val<4 then .store 0 k else .store 1 k

theorem torn_sources_permitted : Compatible (fun _=>0) tornEvents tornSource := by
  unfold Compatible
  intro r hr k
  fin_cases r <;> simp [tornEvents] at hr ⊢
  fin_cases k <;> simp [tornSource,tornEvents] <;> decide +kernel

end PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks

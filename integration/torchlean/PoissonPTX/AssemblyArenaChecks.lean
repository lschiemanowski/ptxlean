import PoissonPTX.AssemblySnapshotPublication

namespace PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def arena : Arena 2 where
  base := 4096
  offsets := 64
  entries := 0
  element := 32
  boundary := 80
  output := 96
  bytes := 112
  entryCount := 3
  elementCount := 3
  small := by decide
  entriesSmall := by decide
  aligned := by decide
  noWrap := by decide
  offsetAligned := by decide
  entryAligned := by decide
  elementAligned := by decide
  boundaryAligned := by decide
  outputAligned := by decide
  offsetsFit := by decide
  entriesFit := by decide
  elementFit := by decide
  boundaryFit := by decide
  outputFit := by decide

/-- Two nodes, three values and a nonzero arena base. The second node is a
boundary node, so the masked entry must replace its sum with zero. -/
def memory : Memory :=
  write32 (write32 (write32 (write32 (write32
    (write64 (write64 (write64
      (write32 (write32 (write32 (fun _ => 0) 4096 0) 4100 1) 4104 2)
      4128 0x4000000000000000) 4136 0x4008000000000000) 4144 0x4010000000000000)
    4160 0) 4164 2) 4168 3) 4176 0) 4180 1

def contents : arena.Contents memory := by
  constructor
  · intro i hi; interval_cases i <;> decide +kernel
  · intro i hi; interval_cases i <;> decide +kernel
  · intro k hk; change k<3 at hk; interval_cases k <;> decide +kernel

def candidate (mask : Bool) (i : Fin 2) := Flow.execute (arena.context i)
  (entryCode 2 64 0 32 mask 80 96) 70 (arena.start memory (fun _ => 0))

def result (mask : Bool) (i : Fin 2) := (candidate mask i).getD (arena.start memory (fun _ => 0))

theorem executed (mask : Bool) (i : Fin 2) : candidate mask i=some (result mask i) := by
  have yes : (candidate mask i).isSome=true := by cases mask <;> fin_cases i <;> decide +kernel
  cases h : candidate mask i with
  | none => simp [h] at yes
  | some out => simp [result,h]

def finished (mask : Bool) : Snapshot.Finished arena memory mask where
  regs := fun _ _ => 0
  final := result mask
  run := fun i => (Flow.execute_sound (executed mask i)).1
  done := fun i => (Flow.execute_sound (executed mask i)).2

theorem row_order (i : Fin 2) : arena.row memory i=Rows.selected [(0,0),(0,1),(1,2)] i.val := by
  fin_cases i <;> decide +kernel

theorem values : arena.value memory 0 false=5 ∧ arena.value memory 1 false=4 ∧
    arena.value memory 0 true=5 ∧ arena.value memory 1 true=0 := by decide +kernel

/-- Both publication orders satisfy the general ordered-scatter theorem. -/
theorem published (mask reverse : Bool) (i : Fin 2) :
    decode (read64 (Snapshot.publish (finished mask) (if reverse then [1,0] else [0,1]))
      (Snapshot.address arena i))=arena.value memory i mask :=
  Snapshot.published_value (finished mask) contents _ (by intro j; cases reverse <;> fin_cases j <;> simp) i

theorem scatter (mask : Bool) (i : Fin 2) :
    decode (read64 (Snapshot.publish (finished mask) [1,0]) (Snapshot.address arena i))=
      if mask=true ∧ read32 memory (4096+80+i.val*4)≠0 then 0 else
        (Rows.contributions [(0,0),(0,1),(1,2)] (arena.elementValue memory)).foldl Correspondence.scatterStep (fun _ => 0) i.val :=
  Snapshot.scatter (finished mask) contents _ row_order [1,0] (by intro j; fin_cases j <;> simp) i

end PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks

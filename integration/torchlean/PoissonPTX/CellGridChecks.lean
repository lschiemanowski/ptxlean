import PoissonPTX.CellGridReference

namespace PtxTorchLean.Poisson.PTX.CellGrid.Checks

/-- A shared store in block zero and a read at the same numeric address in
block one. Equal values must not make this cross-block source admissible. -/
def sharedEvents : List (Event 2) :=
  [(0,.data 0 ⟨.shared,⟨0,true,256,7⟩⟩),(1,.data 0 ⟨.shared,⟨0,false,256,7⟩⟩)]

def foreign : Sources 2 := fun _ _ k => .store (0,0) k

theorem foreign_shared_rejected : ¬Compatible (fun _ => 0) (fun _ _ => 0) sharedEvents foreign := by
  intro compatible
  have owner := shared_source_owner compatible
    (block:=1) (r:=0) (reader:=0) (ra:=⟨.shared,⟨0,false,256,7⟩⟩)
    (by decide +kernel) rfl rfl (k:=0) (writerBlock:=0) (w:=0) (j:=0) rfl
  have different : (0 : Fin 2)≠1 := by decide
  exact different owner

/-- Global byte identities really are shared, while shared identities are not. -/
theorem identities : byteAddress (0 : Fin 2) .global 256=byteAddress 1 .global 256 ∧
    byteAddress (0 : Fin 2) .shared 256≠byteAddress 1 .shared 256 := by
  constructor
  · rfl
  · exact shared_private _ _ (by decide) _ _

def stores : List (Event 2) :=
  [(0,.data 0 ⟨.global,⟨0,true,64,3⟩⟩),
   (1,.data 0 ⟨.global,⟨0,true,72,5⟩⟩),
   (0,.data 0 ⟨.global,⟨1,true,64,9⟩⟩)]

/-- Publication retains each block's actual store order and does not confuse
adjacent words written by different blocks. -/
theorem interleaved_publication : read64 (publish (fun _ => 0) stores) 64=9 ∧
    read64 (publish (fun _ => 0) stores) 72=5 := by decide +kernel

def seed : PTX.State := {
  pc:=0, regs:=fun _ => 0, global:=fun _ => 0, shared:=fun _ => 0,
  globalStart:=0, globalBytes:=512, sharedStart:=256, sharedBytes:=224 }

def start : CellWhole.State := ⟨⟨fun _ => seed,Ptx.Barrier.reset 0,none⟩,fun _ => false,fun _ => false⟩
def launch : Launch 2 := ⟨2,fun _ space => match space with | .global => 0 | .shared => 256,
  192,224,256,fun block lane => ⟨0,BitVec.ofNat 32 lane.val,BitVec.ofNat 32 block.val⟩⟩
def after : CellWhole.State :=
  CellWhole.entryState start (CellEntry.setLane (CellWhole.entry start) 0
    (CellPrologue.assign (CellEntry.lane (CellWhole.entry start) 0) 3 256))

theorem first_step (block : Fin 2) :
    CellWhole.Step (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block) 0 start ⟨after,[],[]⟩ := by
  apply CellWhole.Step.entry (out:=⟨CellEntry.setLane (CellWhole.entry start) 0
    (CellPrologue.assign (CellEntry.lane (CellWhole.entry start) 0) 3 256),[],[]⟩) rfl
  refine ⟨rfl,.setup (.context 3 .scratch),rfl,?_⟩
  exact CellEntry.Dispatch.setup rfl

/-- Two fetched setup instructions in different blocks change the selected
block only. The general projection theorem sees the same actual local step. -/
theorem two_blocks : Runs launch (fun _ => start) [] []
    (Function.update (Function.update (fun _ => start) (0 : Fin 2) after) 1 after) := by
  apply Runs.cons (block:=0) (thread:=0) (out:=⟨after,[],[]⟩) (first_step 0)
  apply Runs.cons (block:=1) (thread:=0) (out:=⟨after,[],[]⟩)
  · simpa using first_step 1
  · exact .nil

theorem projected_step : CellWhole.Runs (config (1 : Fin 2)) (launch.bases 1) 1
    launch.width launch.cells launch.source launch.output (launch.context 1) start [] [] after := by
  simpa [forBlock] using project two_blocks 1

end PtxTorchLean.Poisson.PTX.CellGrid.Checks

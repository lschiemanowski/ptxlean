import PoissonPTX.CellAssemblyWitness

namespace PtxTorchLean.Poisson.PTX.CellAssemblyWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
attribute [local irreducible] prefixResult bodyResult events final

def layout (u : Fin 32) (active : u.val<4) :
    CellGather.Layout (CellEntry.Local.beforeGather (CellPrologue.threadContext bases 0 u) 2 (CellEntry.lane start u)) 2 192 224 where
  cellCount := 1
  pointCount := 1
  globalBase := by rfl
  sharedBase := by rfl
  globalAligned := by change 0%8=0; decide
  sharedAligned := by change 0%8=0; decide
  cellsAligned := by decide
  sourceAligned := by decide
  cell := by change 0<1; decide
  active := by
    have small : u.val<4294967296 := by have := u.isLt; omega
    have wide : u.val<18446744073709551616 := by have := u.isLt; omega
    simpa [CellEntry.Local.beforeGather,CellPrologue.finish,CellPrologue.threadContext,
      advance,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt wide] using active
  widthBound := by decide
  indexFits := by decide
  cellsFit := by change 192+1*(2*2)*4≤512; decide
  sourceFit := by change 224+1*8≤512; decide
  sharedFit := by change 7*2*2*8≤224; decide
  globalNoWrap := by change 0+512≤2^64; decide
  sharedNoWrap := by change 0+224≤2^64; decide
  connectivity := by
    intro k inside
    change (read32 memory (192+k*4)).toNat<1
    interval_cases k <;> decide +kernel

theorem coefficients : CoefficientRepresentation.Represents operator bases initial where
  shape := rfl
  b := by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
  d := by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
  w := by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def execution : CellWhole.Execution operator values 0 where
  cfg := cfg
  bases := bases
  cells := 192
  source := 224
  output := 256
  bodyContext := context
  memory := initial
  start := CellWhole.begin start
  final := final
  events := events
  indices := prefixResult.indices
  allSources := Concurrent.ZeroSources.source events
  indexChoices := fun _ _ => .initial
  generation := 0
  run := actual
  aligned := by intro t h; simp [CellWhole.begin,start,Ptx.Barrier.reset] at h
  initial := by intro _; rfl
  pcs := by intro _; rfl
  running := by intro _; rfl
  positive := by decide
  small := by decide
  space := by decide
  layout := layout
  cellsBefore := by intro u active; change 192+1*(2*2)*4≤256; decide
  sourceBefore := by intro u active; change 224+1*8≤256; decide
  connectivity := by
    intro u active k inside
    change k<4 at inside
    simp only [CellWhole.begin,start,seed,CellWhole.Zero.seed,operator,Nat.zero_add]
    interval_cases k <;> decide +kernel
  contents := by
    intro u active k inside
    change k<1 at inside
    change decode (read64 memory (224+k*8))=values[k]!
    interval_cases k
    decide +kernel
  coefficients := coefficients
  lo := by decide
  hi := by decide
  reset := rfl
  bounds := by intro u; fin_cases u <;> decide +kernel
  offset := by decide
  jointIndices := indices_admitted
  joint := admitted
  performed := performed
  finished := by intro u active; have pc := (returned u).2; change 21+(Concurrent.CellConsumer.WithOutput.front 2).length+5≤_; omega

def family : CellWhole.Family operator values where
  base := 0
  output := 256
  memory := memory
  small := by decide
  execution := fun i => by
    have zero : i.val=0 := by
      have bound := i.isLt
      change i.val<1 at bound
      omega
    simpa [zero] using execution
  sameInitial := by intro i; fin_cases i; rfl
  sameCTA := by intro i; fin_cases i; rfl
  sameBase := by intro i; fin_cases i; rfl
  sameOutput := by intro i; fin_cases i; rfl

theorem meshShape : OperatorMesh operator where
  width := by intro e bound; change e<1 at bound; interval_cases e; rfl
  nodes := by intro e bound k inside; change e<1 at bound; change k<4 at inside; interval_cases e <;> interval_cases k <;> decide

def arena : Assembly.Arena operator.mesh.points.size where
  base := 0
  offsets := 208
  entries := 240
  element := 256
  boundary := 232
  output := 216
  bytes := 512
  entryCount := 4
  elementCount := 4
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

theorem tables_checked : arena.checkRows memory (Assembly.nodeRows 1 (Assembly.MeshRows.locations meshShape.connectivity))=true := by decide +kernel

theorem separated : arena.InputSeparation := by constructor <;> unfold Assembly.Arena.FieldApart <;> decide +kernel

theorem numerical : meshShape.operator rfl values ⟨0,by decide⟩=8 := by decide +kernel

/-- A false read cannot be justified by merely choosing initialization. -/
theorem forged_word_rejected : Concurrent.WordSourceCheck.check initial
    [Concurrent.Event.data (0 : Fin 32) ⟨.global,⟨0,false,224,0⟩⟩]=false := by decide +kernel

/-- A nonzero admitted full cell is followed by an admitted returning assembly
launch. Its published result is eight by the composition theorem. -/
theorem composed : ∃ words indices final,
    Flow.Parallel.Runs arena.context (Assembly.entryCode 1 208 240 256 false 232 216)
      (fun _ => arena.start (family.publish memory [⟨0,by decide⟩]) (fun _ => 0)) words indices final ∧
    (∀ i, (final i).halted=true) ∧
    Concurrent.Visibility.Compatible
      (fun space => match space with | .global => family.publish memory [⟨0,by decide⟩] | .shared => fun _ => 0)
      words (fun _ _ => .initial) ∧
    IndexSources.Compatible (family.publish memory [⟨0,by decide⟩]) words indices (fun _ _ => .initial) ∧
    decode (read64 (Concurrent.GlobalPublication.publish (family.publish memory [⟨0,by decide⟩]) words) 216)=8 := by
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible,correct⟩ :=
    cell_assembly_exists family meshShape rfl [⟨0,by decide⟩] (by intro i; fin_cases i; simp) arena rfl rfl
      (by decide) (by decide) (by decide) (arena.checkRows_sound tables_checked) separated (fun _ _ => 0) false
  refine ⟨words,indices,final,run,done,compatible,indexCompatible,?_⟩
  have value := correct ⟨0,by decide⟩
  simpa only [Assembly.Snapshot.address,show family.memory=memory from rfl,
    show arena.base.toNat+arena.output.toNat+0*8=216 from rfl,
    Bool.false_eq_true,false_and,ite_false,numerical] using value

end PtxTorchLean.Poisson.PTX.CellAssemblyWitness

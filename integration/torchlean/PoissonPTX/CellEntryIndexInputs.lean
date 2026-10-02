import PoissonPTX.CellEntryInputLayout

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context} {later : List (Concurrent.Event n)}

theorem index_instruction {pc : Nat}
    (fetch : (program width cells source)[pc]?=some (.gather (.load32 dst addr))) :
    pc=12 ∧ dst=18 ∧ addr=2 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

/-- Inspect the actual four-byte read record, before reasoning about its value. -/
theorem index_origin (step : Step cfg ctx (program width cells source) selected s out)
    (member : (owner,access)∈out.indices) :
    selected=owner ∧ (s.core.lanes owner).pc=12 ∧ access.pc=12 ∧
      access.address=((s.core.lanes owner).regs 2).toNat := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | sync => simp only [synchronize] at member; simp at member
  | gather hd =>
    have same : ‹Option IndexSources.Access›=some access ∧ selected=owner := by simpa using member
    rcases same with ⟨same,rfl⟩
    rw [same] at hd
    cases hd with
    | load32 valid =>
      obtain ⟨pc,rfl,rfl⟩ := index_instruction fetch
      simp [pc]

/-- Bounds of every actual connectivity read, derived without chosen read bits. -/
theorem index_step_bound (step : Step cfg ctx (program width cells source) selected s out)
    (control : ∀ u, Ready (ctx u) width (lane s u))
    (active : ∀ u, Active (lane s u)) (ready : ∀ u, IndexReady (ctx u) width cells (lane s u))
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout memory (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena) (member : (owner,access)∈out.indices) :
    access.address+4≤arena.toNat+output.toNat := by
  obtain ⟨_,pc,_,address⟩ := index_origin step member
  have live := active owner (by change 8≤(s.core.lanes owner).pc; omega)
    (by change (s.core.lanes owner).pc<20; omega)
  have guard := (control owner).2.2.2.2.1 (by change 5≤(s.core.lanes owner).pc; omega)
  rw [guard] at live
  have inputs := layout owner (of_decide_eq_true live)
  have reg := (ready owner).2.2.2 pc
  change (s.core.lanes owner).regs 2=_ at reg
  rw [address,reg]
  simpa only [base] using index_below inputs

theorem index_bounds (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (control : ∀ u, Ready (ctx u) width (lane s u))
    (active : ∀ u, Active (lane s u)) (ready : ∀ u, IndexReady (ctx u) width cells (lane s u))
    (positive : 0<width) (fits : width*width<2^32)
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout memory (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena) (member : (owner,access)∈indices) :
    access.address+4≤arena.toNat+output.toNat := by
  induction run with
  | nil => simp at member
  | cons one rest ih =>
    rcases List.mem_append.mp member with first | later
    · exact index_step_bound one control active ready layout base first
    · exact ih (step_aligned one aligned) (step one aligned control positive fits)
        (active_step one aligned active) (index_step one aligned control ready) later

/-- Joint-history sources fix each index to initialization once the actual
output stores have been proved beyond the input fence. -/
theorem joint_indices (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (pcs : ∀ u, (s.core.lanes u).pc=0)
    (positive : 0<width) (fits : width*width<2^32)
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout memory (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena)
    (stores : ∀ owner access, Concurrent.Event.data owner access∈later →
      access.data.store=true → access.space=.global → arena.toNat+output.toNat≤access.data.address)
    (compatible : IndexSources.Compatible memory (events++later) indices chosen) :
    Indices memory indices := by
  intro owner access member
  obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
  apply IndexSources.read_only_value compatible observed
  apply IndexSources.readonly_of_disjoint
  intro w writer wa seen store global
  have readBound := index_bounds run aligned (fun u => initial (s:=lane s u) (pcs u))
    (fun u => active_initial (s:=lane s u) (pcs u))
    (fun u => index_initial (s:=lane s u) (pcs u)) positive fits layout base member
  rcases List.mem_append.mp (List.mem_of_getElem? seen) with first | second
  · exact False.elim (no_global_store run first store global)
  · right; have := stores writer wa second store global; omega

/-- Derived prefix admission uses initialization for every index byte. -/
theorem indices_compatible (values : Indices memory indices) :
    IndexSources.Compatible memory events indices (fun _ _ => .initial) := by
  intro r owner access observed k
  have h := values owner access (List.mem_of_getElem? observed)
  simp only [h,IndexSources.byte_read32]

end PtxTorchLean.Poisson.PTX.CellEntry.Control

import PoissonPTX.CellEntrySourceAddress

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

/-- The initial connectivity value bounds the source-vector address. -/
theorem source_below (layout : InputLayout memory ctx width cells source output) :
    (ctx.arena+sourceScale memory ctx width cells+source).toNat+8≤ctx.arena.toNat+output.toNat := by
  have node : (nodeWord memory ctx width cells).toNat<layout.pointCount := by
    simpa only [nodeWord,index_address layout] using layout.nodeBound
  have scaled : (nodeWord memory ctx width cells).toNat*8<2^64 := by
    have := (nodeWord memory ctx width cells).isLt; omega
  have total : ctx.arena.toNat+(nodeWord memory ctx width cells).toNat*8+source.toNat+8≤2^64 := by
    have := layout.sourceEnd; have := layout.noWrap; omega
  have middle : ctx.arena.toNat+(nodeWord memory ctx width cells).toNat*8<2^64 := by omega
  have last : ctx.arena.toNat+(nodeWord memory ctx width cells).toNat*8+source.toNat<2^64 := by omega
  simp only [BitVec.toNat_add,sourceScale,BitVec.toNat_ofNat,Nat.mod_eq_of_lt scaled,
    Nat.mod_eq_of_lt middle,Nat.mod_eq_of_lt last]
  have := layout.sourceEnd; omega

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context} {later : List (Concurrent.Event n)}

theorem word_instruction {pc : Nat}
    (fetch : (program width cells source)[pc]?=some (.gather (.data (.load64 sp dst addr)))) :
    pc=16 ∧ sp=.global ∧ dst=11 ∧ addr=.reg 2 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

theorem word_origin (step : Step cfg ctx (program width cells source) selected s out)
    (member : Concurrent.Event.data owner access∈out.events) (read : access.data.store=false) :
    selected=owner ∧ (s.core.lanes owner).pc=16 ∧ access.space=.global ∧
      access.data.address=((s.core.lanes owner).regs 2).toNat := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | sync =>
    simp only [synchronize,Concurrent.synchronize] at member
    split at member <;> simp_all
  | gather hd =>
    have same : ‹Option Concurrent.Access›=some access ∧ selected=owner := by simpa using member
    rcases same with ⟨same,rfl⟩
    rw [same] at hd
    cases hd with
    | data he => cases he with
      | store => simp at read
      | load valid =>
        obtain ⟨pc,rfl,rfl,rfl⟩ := word_instruction fetch
        simp [pc,Operand.eval]

theorem word_step_bound (step : Step cfg ctx (program width cells source) selected s out)
    (control : ∀ u, Ready (ctx u) width (lane s u))
    (active : ∀ u, Active (lane s u))
    (ready : ∀ u, SourceReady memory (ctx u) width cells source (lane s u))
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout memory (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena) (member : Concurrent.Event.data owner access∈out.events)
    (read : access.data.store=false) : access.space=.global ∧ access.data.address+8≤arena.toNat+output.toNat := by
  obtain ⟨_,pc,global,address⟩ := word_origin step member read
  have live := active owner (by change 8≤(s.core.lanes owner).pc; omega)
    (by change (s.core.lanes owner).pc<20; omega)
  have guard := (control owner).2.2.2.2.1 (by change 5≤(s.core.lanes owner).pc; omega)
  rw [guard] at live
  have inputs := layout owner (of_decide_eq_true live)
  have reg := (ready owner).2.2.2 pc
  refine ⟨global,?_⟩
  change (s.core.lanes owner).regs 2=_ at reg
  rw [address,reg]
  simpa only [base] using source_below inputs

theorem word_bounds (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (control : ∀ u, Ready (ctx u) width (lane s u))
    (active : ∀ u, Active (lane s u)) (index : ∀ u, IndexReady (ctx u) width cells (lane s u))
    (ready : ∀ u, SourceReady memory (ctx u) width cells source (lane s u))
    (positive : 0<width) (fits : width*width<2^32) (values : Indices memory indices)
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout memory (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena) (member : Concurrent.Event.data owner access∈events)
    (read : access.data.store=false) : access.space=.global ∧ access.data.address+8≤arena.toNat+output.toNat := by
  induction run with
  | nil => simp at member
  | cons one rest ih =>
    rcases List.mem_append.mp member with first | later
    · exact word_step_bound one control active ready layout base first read
    · exact ih (step_aligned one aligned) (step one aligned control positive fits)
        (active_step one aligned active) (index_step one aligned control index)
        (source_step one aligned control index ready
          (fun u a ha => values u a (List.mem_append_left _ ha)))
        (fun u a ha => values u a (List.mem_append_right _ ha)) later

/-- Derived word-source admission for the prefix. No gather read value is a
premise: the index values used in address derivation were forced separately. -/
theorem joint_words (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (pcs : ∀ u, (s.core.lanes u).pc=0)
    (positive : 0<width) (fits : width*width<2^32) (values : Indices (memory .global) indices)
    (layout : ∀ u, (ctx u).lane.toNat<width*width → InputLayout (memory .global) (ctx u) width cells source output)
    (base : ∀ u, (ctx u).arena=arena)
    (stores : ∀ owner access, Concurrent.Event.data owner access∈later →
      access.data.store=true → access.space=.global → arena.toNat+output.toNat≤access.data.address)
    (compatible : Concurrent.Visibility.Compatible memory (events++later) chosen) :
    Concurrent.Visibility.Compatible memory events (fun _ _ => .initial) := by
  intro r owner access observed read k
  have member := List.mem_of_getElem? observed
  have bound := word_bounds run aligned (fun u => initial (s:=lane s u) (pcs u))
    (fun u => active_initial (s:=lane s u) (pcs u))
    (fun u => index_initial (s:=lane s u) (pcs u))
    (fun u => source_initial (s:=lane s u) (pcs u)) positive fits values layout base member read
  have seen : (events++later)[r]?=some (.data owner access) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp observed).1]; exact observed
  have correct := Concurrent.Visibility.read_only_value compatible seen read (by
    intro w writer wa hw store space j k
    rw [bound.1] at space
    rcases List.mem_append.mp (List.mem_of_getElem? hw) with first | second
    · exact False.elim (no_global_store run first store space)
    · have lower := stores writer wa second store space
      have := j.isLt; have := k.isLt; omega)
  simp only [correct,Sources.byte_read64]

end PtxTorchLean.Poisson.PTX.CellEntry.Control

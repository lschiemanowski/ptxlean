import PoissonPTX.CellCandidate

namespace PtxTorchLean.Poisson.PTX.CellWhole
open Concurrent.CellConsumer.WithOutput
variable {o : Operator} {values : Array Float} {cell : BitVec 32}

/-- Raw layout facts already supply the input fence, independently of sources. -/
def Candidate.inputLayout (execution : Candidate o values cell) (u : Fin 32)
    (active : u.val<o.nodes.size*o.nodes.size) :
    CellEntry.Control.InputLayout (execution.memory .global)
      (CellPrologue.threadContext execution.bases cell u) o.nodes.size execution.cells execution.source execution.output :=
  CellEntry.Control.InputLayout.of_gather (execution.layout u active) (execution.initial u)
    (execution.cellsBefore u active) (execution.sourceBefore u active)
    (by have bound := (execution.bounds u).2; change (execution.bases .global).toNat+execution.output.toNat≤2^64; omega)

/-- Complete candidate execution necessarily passed its first barrier. -/
theorem Candidate.past (execution : Candidate o values cell) :
    20<(execution.final.core.lanes (0 : Fin 32)).pc := by
  have active : (0 : Fin 32).val<o.nodes.size*o.nodes.size := by
    have := execution.positive; change 0<o.nodes.size*o.nodes.size; nlinarith
  have done := execution.finished 0 active
  omega

/-- Every actual connectivity access is below the cell-output fence before any
reasoning about its chosen bits. -/
theorem Candidate.index_bound (execution : Candidate o values cell)
    (member : (owner,access)∈execution.indices) :
    access.address+4≤(execution.bases .global).toNat+execution.output.toNat := by
  obtain ⟨before,after,ready,localFinal,eventEq,first,done,site,finalEq,body⟩ :=
    executions execution.run execution.aligned execution.pcs execution.running 0 execution.past
  apply CellEntry.Control.index_bounds (memory:=execution.memory .global) first execution.aligned
    (fun u => CellEntry.Control.initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
    (fun u => CellEntry.Control.active_initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
    (fun u => CellEntry.Control.index_initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
    execution.positive (by have := execution.small; omega) _ (fun _ => rfl) member
  intro u live
  exact execution.inputLayout u (by simpa only [CellEntry.context_lane] using live)

/-- Once connectivity bytes have been forced to initialization, every actual
global word read is below the output fence. Body coefficient addresses require
no chosen-value premise. -/
theorem Candidate.word_bound (execution : Candidate o values cell)
    (indexValues : CellEntry.Indices (execution.memory .global) execution.indices)
    (member : Concurrent.Event.data owner access∈execution.events)
    (read : access.data.store=false) (global : access.space=.global) :
    access.data.address+8≤(execution.bases .global).toNat+execution.output.toNat := by
  obtain ⟨before,after,ready,localFinal,eventEq,first,done,site,finalEq,body⟩ :=
    executions execution.run execution.aligned execution.pcs execution.running 0 execution.past
  rw [eventEq] at member
  rcases List.mem_append.mp member with prefixMember | bodyMember
  · exact (CellEntry.Control.word_bounds first execution.aligned
      (fun u => CellEntry.Control.initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
      (fun u => CellEntry.Control.active_initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
      (fun u => CellEntry.Control.index_initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
      (fun u => CellEntry.Control.source_initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
      execution.positive (by have := execution.small; omega) indexValues
      (fun u live => execution.inputLayout u (by simpa only [CellEntry.context_lane] using live))
      (fun _ => rfl) prefixMember read).2
  · obtain ⟨event,localMember,eq⟩ := List.mem_map.mp bodyMember
    cases event with
    | barrier => simp [Relocate.event] at eq
    | data thread recorded =>
      simp only [Relocate.event,Concurrent.Event.data.injEq] at eq
      obtain ⟨rfl,rfl⟩ := eq
      change recorded.data.store=false at read
      change recorded.space=.global at global
      obtain ⟨launch⟩ := CellEntry.Control.launch first execution.aligned execution.pcs done
        execution.positive (by have := execution.small; omega) execution.space
      obtain ⟨small,shadow,arithmetic,embedding,omitted,related⟩ :=
        arithmetic_filtered execution.lo execution.hi body launch.aligned launch.pcs
      obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp localMember
      have kept : Concurrent.Projection.Retained embedding r := by
        by_contra missing
        have kind := omitted r (.data thread recorded) observed missing
        simp [OutputEvent,read] at kind
      obtain ⟨v,inside,position⟩ := kept
      have seen : small[v]?=some (.data thread recorded) := by
        rw [← embedding.fetch v inside,position,observed]
      have nowrap : (execution.bases .global).toNat+Concurrent.CellConsumer.Coefficients.extent o.nodes.size≤2^64 := by
        have bound := (execution.bounds 0).2
        have offset := execution.offset
        omega
      have bound := Concurrent.CellConsumer.Coefficients.read_bounds launch execution.lo execution.hi
        arithmetic nowrap (List.mem_of_getElem? seen) read global
      change recorded.data.address+8≤_
      have offset := execution.offset
      omega

end PtxTorchLean.Poisson.PTX.CellWhole

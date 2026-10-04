import PoissonPTX.DotAddress

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem tail_address (pc : s.core.pc=96+slot) (fetch : (tail output)[slot]?=some i)
    (actual : Flow.Observed.Eval ctx i s t access index)
    (ready : AddressReady ctx.arena output s) : AddressReady ctx.arena output t := by
  have bound : slot<8 := by
    have h := (List.getElem?_eq_some_iff.mp fetch).1
    simpa [tail] using h
  interval_cases slot <;> simp [tail] at fetch <;> cases fetch
  all_goals cases actual
  all_goals try { rename_i ordinary; exact False.elim (ordinary _ rfl) }
  all_goals (first | cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval | skip)
  all_goals simp_all [Concurrent.ordinary,AddressReady,assign,advance,Operand.eval,
    Flow.simple,Flow.next,Flow.halt,put]
  all_goals split <;> simp_all

theorem flow_address
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index)
    (ready : AddressReady ctx.arena output s) : AddressReady ctx.arena output t := by
  by_cases before : s.core.pc<20
  · rw [input_fetch before] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    exact input_address found actual ready
  · by_cases middle : s.core.pc<96
    · exact tree_address (by omega) middle fetch actual ready
    · have position : s.core.pc=96+(s.core.pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      exact tail_address position found actual ready

theorem sync_address {ctx : Kernel.Context}
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.sync resource))
    (ready : AddressReady ctx.arena output s) : AddressReady ctx.arena output (Flow.next s) := by
  have before : 20≤s.core.pc := by
    by_contra notBefore
    exact NativeFlow.no_prefix_sync input_region (by simp only [DotInput.input_length]; omega) fetch
  have inside : s.core.pc<96 := by
    by_contra notInside
    have position : s.core.pc=96+(s.core.pc-96) := by omega
    rw [position,tail_fetch] at fetch
    cases (tail output)[s.core.pc-96]? <;> simp at fetch
  apply address_ready_early (early:=by change s.core.pc+1<100; omega)
  intro _
  exact ready.1 (by omega)

theorem run_addresses
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) s events indices t)
    (aligned : Aligned s.core) (entry : ∀ owner, (s.core.lanes owner).pc=0) :
    ∀ owner, AddressReady (ctx owner).arena output (NativeFlow.lane t owner) := by
  apply NativeFlow.runs_lanes run aligned
    (fun owner => address_ready_initial (entry owner))
  · intro owner i before after access index ready fetch actual
    exact flow_address fetch actual ready
  · intro owner before resource ready fetch
    exact sync_address fetch ready

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

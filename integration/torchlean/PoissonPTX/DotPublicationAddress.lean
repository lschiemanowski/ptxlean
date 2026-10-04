import PoissonPTX.DotPublicationSyntax

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Scratch registers are produced by the two instructions preceding the
initial store. They are not assumed to hold a convenient address on entry. -/
def PublicationAddress (s : Flow.State) : Prop :=
  (s.core.pc=21 → s.core.regs 1=wide s.core 14) ∧
  (s.core.pc=22 → s.core.regs 2=s.core.regs 3+wide s.core 14)

theorem publication_address_early (bound : s.core.pc≤20) : PublicationAddress s :=
  ⟨by intro h; omega,by intro h; omega⟩

theorem publication_address_late (bound : 23≤s.core.pc) : PublicationAddress s :=
  ⟨by intro h; omega,by intro h; omega⟩

theorem publication_address_flow
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index) (ready : PublicationAddress s) :
    PublicationAddress t := by
  by_cases input : s.core.pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    exact publication_address_early (NativeFlow.eval_upper actual input (input_syntax (List.mem_of_getElem? found)).1)
  · by_cases past : 23≤s.core.pc
    · exact publication_address_late (NativeFlow.eval_lower actual past (outside_publication_targets (by omega) fetch))
    · have lower : 20≤s.core.pc := by omega
      have upper : s.core.pc≤22 := by omega
      have position : s.core.pc=20+(s.core.pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      clear position
      generalize counter : s.core.pc=pc at lower upper fetch
      interval_cases pc <;> simp only [Nat.reduceSub] at fetch
      all_goals
        change some _=some (NativeFlow.Instr.flow i) at fetch
        have equal := Option.some.inj fetch
        cases equal
        cases actual
      all_goals try { rename_i ordinary; exact False.elim (ordinary _ rfl) }
      all_goals cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval
      all_goals simp_all [Concurrent.ordinary,PublicationAddress,assign,advance,Operand.eval,wide,put]

theorem publication_address_sync
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.sync resource)) :
    PublicationAddress (Flow.next s) := by
  apply publication_address_late
  have after : 23≤s.core.pc := by
    by_contra before
    exact no_early_sync (by omega) fetch
  change 23≤s.core.pc+1
  omega

theorem publication_addresses
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0) :
    ∀ owner, PublicationAddress (NativeFlow.lane final owner) := by
  apply NativeFlow.runs_lanes run aligned (fun owner => publication_address_early (by simp [NativeFlow.lane,entry]))
  · intro owner i before after access index ready fetch actual
    exact publication_address_flow fetch actual ready
  · intro owner before resource _ fetch
    exact publication_address_sync fetch

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

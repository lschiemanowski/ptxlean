import PoissonPTX.ReductionReads
import PoissonPTX.ConcurrentValues

/-! The numerical tree follows the instruction order, including each rounded
addition. It is a computation on decoded binary64 values, not an exact-real
sum and not a demand for canonical NaN payloads in actual stored words. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric

/-- State after k halving rounds; lanes outside the active range retain values. -/
def values (input : Nat → Float) : Nat → Nat → Float
  | 0 => input
  | k+1 => Binary64.round (256 / 2^(k+1)) (values input k)

theorem final_value : values input 8 0=Binary64.reduce256 input := rfl

def initial (input : Nat → Float) : Values.Table 256 :=
  Function.update Values.empty 8 (some (fun t => input t.val))

def loads (input : Nat → Float) (k : Fin 8) (pc : Nat) : Option (Fin 256 → Float) :=
  if pc=readPC k false then some (fun t => values input k.val t.val)
  else if pc=readPC k true then some (fun t => values input k.val (t.val+active (current k)))
  else none

theorem initial_tag : Values.tag program (initial input) loadContract (site 0) 8=
    some (fun t => input t.val) := rfl

theorem update_tag (input : Nat → Float) (k : Fin 8) :
    Values.tag program (initial input) (loads input k) (site (current k)) 8=
      some (fun t => values input k.val t.val + values input k.val (t.val+active (current k))) := by
  fin_cases k <;> rfl

theorem checked_targets : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.skip _ target) => decide (target=11 ∨ target=19 ∨ target=27 ∨ target=35 ∨
        target=43 ∨ target=51 ∨ target=59 ∨ target=67)
    | _ => true)=true := by decide +kernel

theorem entries : Values.Entries program (initial input) loadContract := by
  intro pc count target fetch thread state
  have h := checked_targets ⟨pc,by
    have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  simp only [fetch,decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Values.empty_ready

variable {events : List (Event 256)} {thread : Fin 256} {access : Access} {w : Nat}

/-- The register analysis reads the actual store source, rather than taking a
presumed arithmetic answer or local execution as a premise. -/
theorem stored {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (inputs : ∀ t, decode ((start.lanes t).regs 8)=input t.val)
    (reads : Values.Reads loadContract events) (k : Fin 9)
    (known : Values.tag program (initial input) loadContract (site k) 8=some answer)
    (observed : events[w]?=some (.data thread access)) (atSite : access.data.pc=site k) :
    decode access.data.value=answer thread := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ :=
    run_access_prefix run (List.mem_of_getElem? observed)
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have pc := access_pc hd
  have atStore : (before.lanes thread).pc=site k := pc.symm.trans atSite
  have inv : Values.Invariant program (initial input) loadContract start := by
    intro t r f hf
    rw [entry] at hf
    simp only [Values.tag,initial,Function.update_apply,Values.empty] at hf
    split at hf
    · rename_i eq; subst r; cases hf; exact inputs t
    · cases hf
  have ready := Values.runs_invariant hp aligned inv entries
    (fun t a h => reads t a (by rw [he]; exact List.mem_append_left _ (List.mem_append_left _ h))) thread
  rw [atStore] at ready
  have result := ready 8 answer known
  rw [atStore,store_fetch k] at fetch
  cases fetch
  cases hd with | store => exact result

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric

import PoissonPTX.ContractionLoads

namespace PtxTorchLean.Poisson.PTX.Contraction

/-- Separate rounded multiply and add, never a fused operation. -/
def mac (acc : Nat) : List Op :=
  [.fp .mul 10 (.reg 4) (.reg 5), .fp .add acc (.reg acc) (.reg 10)]

def term (width k acc : Nat) (a b : Matrix) : List Op :=
  loadCode width k 4 a ++ loadCode width k 5 b ++ mac acc

def terms (width acc : Nat) (a b : Matrix) (ks : List Nat) : List Op :=
  ks.flatMap fun k => term width k acc a b

def program (width acc : Nat) (a b : Matrix) : List Op :=
  .mov acc (.imm 0) :: terms width acc a b (List.range width)

/-- Registers 8 and 9 are the two actual accumulators in the generated cell. -/
def Accumulator (acc : Nat) : Prop := acc=8 ∨ acc=9

theorem mac_correct (allowed : Accumulator acc) (h : Block (mac acc) s t) :
    decode (t.regs acc) = decode (s.regs acc) + decode (s.regs 4)*decode (s.regs 5) ∧
    Stable s t := by
  rcases allowed with rfl|rfl <;>
    cases h with | cons hm rest =>
      cases hm with | fp hm =>
        cases rest with | cons ha rest =>
          cases ha with | fp ha =>
            cases rest
            simp_all [FP.Result,FP.apply,Operand.eval,assign,advance,Stable,environment]

theorem mac_exists (s : State) (acc : Nat) : ∃ t, Block (mac acc) s t := by
  obtain ⟨p,hp⟩ := FP.result_exists .mul (s.regs 4) (s.regs 5)
  obtain ⟨v,hv⟩ := FP.result_exists .add ((assign s 10 p).regs acc) p
  refine ⟨assign (assign s 10 p) acc v,.cons (.fp hp) (.cons (.fp ?_) .nil)⟩
  simpa [Operand.eval,assign] using hv

theorem term_correct (allowed : Accumulator acc)
    (va : Valid s width k a) (vb : Valid s width k b)
    (h : Block (term width k acc a b) s t) :
    decode (t.regs acc) = decode (s.regs acc) + value s width k a * value s width k b ∧
    Stable s t := by
  obtain ⟨u,hloads,hmac⟩ := block_split (loadCode width k 4 a ++ loadCode width k 5 b) (mac acc) h
  obtain ⟨v,hv,hb⟩ := block_split _ _ hloads
  have ev := load_eq hv va
  subst v
  have hs := loaded_stable s width k 4 a (by decide) (by decide) (by decide) (by decide)
  have eu := load_eq hb ((stable_valid hs).mpr vb)
  subst u
  have hs' := loaded_stable (loaded s width k 4 a) width k 5 b (by decide) (by decide) (by decide) (by decide)
  obtain ⟨answer,frame⟩ := mac_correct allowed hmac
  refine ⟨?_,stable_trans (stable_trans hs hs') frame⟩
  have right : decode (read64 ((loaded s width k 4 a).memory b.space)
      (location (loaded s width k 4 a) width k b).toNat) = value s width k b := stable_value hs
  rcases allowed with rfl|rfl <;>
    simpa [loaded_preserves,loaded_reg,right,value] using answer

theorem term_exists (s : State) (width k acc : Nat) (a b : Matrix)
    (va : Valid s width k a) (vb : Valid s width k b) :
    ∃ t, Block (term width k acc a b) s t := by
  have hs := loaded_stable s width k 4 a (by decide) (by decide) (by decide) (by decide)
  have hb := load_run (loaded s width k 4 a) width k 5 b ((stable_valid hs).mpr vb)
  obtain ⟨t,ht⟩ := mac_exists (loaded (loaded s width k 4 a) width k 5 b) acc
  exact ⟨t,block_append (block_append (run_sound (load_run s width k 4 a va)) (run_sound hb)) ht⟩

/-- All completed block executions, including noncanonical permitted NaN bits. -/
theorem terms_correct (allowed : Accumulator acc)
    (valid : ∀ k∈ks, Valid s width k a ∧ Valid s width k b)
    (h : Block (terms width acc a b ks) s t) :
    decode (t.regs acc) = ks.foldl (fun z k => z + value s width k a * value s width k b) (decode (s.regs acc)) ∧
    Stable s t := by
  induction ks generalizing s with
  | nil => cases h; exact ⟨rfl,stable_refl _⟩
  | cons k ks ih =>
    obtain ⟨u,first,rest⟩ := block_split _ _ h
    obtain ⟨val,frame⟩ := term_correct allowed (valid k (by simp)).1 (valid k (by simp)).2 first
    have tail := ih (s := u) (by
      intro j hj
      exact ⟨(stable_valid frame).mpr (valid j (by simp [hj])).1,
             (stable_valid frame).mpr (valid j (by simp [hj])).2⟩) rest
    refine ⟨?_,stable_trans frame tail.2⟩
    rw [tail.1]
    simp only [List.foldl_cons,stable_value frame,val]

theorem terms_exists (s : State) (allowed : Accumulator acc)
    (valid : ∀ k∈ks, Valid s width k a ∧ Valid s width k b) :
    ∃ t, Block (terms width acc a b ks) s t := by
  induction ks generalizing s with
  | nil => exact ⟨s,.nil⟩
  | cons k ks ih =>
    obtain ⟨u,hu⟩ := term_exists s width k acc a b (valid k (by simp)).1 (valid k (by simp)).2
    have frame := (term_correct allowed (valid k (by simp)).1 (valid k (by simp)).2 hu).2
    obtain ⟨t,ht⟩ := ih u (by
      intro j hj
      exact ⟨(stable_valid frame).mpr (valid j (by simp [hj])).1,
             (stable_valid frame).mpr (valid j (by simp [hj])).2⟩)
    exact ⟨t,block_append hu ht⟩

theorem correct (allowed : Accumulator acc)
    (valid : ∀ k<width, Valid s width k a ∧ Valid s width k b)
    (h : Block (program width acc a b) s t) :
    decode (t.regs acc) = (List.range width).foldl
      (fun z k => z + value s width k a * value s width k b) 0 ∧ Stable s t := by
  cases h with | cons hi rest =>
    cases hi
    change Block (terms width acc a b (List.range width)) (assign s acc 0) t at rest
    have frame : Stable s (assign s acc 0) := by
      rcases allowed with rfl|rfl <;> exact stable_assign _ _ _ (by decide) (by decide) (by decide) (by decide)
    have result := terms_correct allowed (by
      intro k hk
      exact ⟨(stable_valid frame).mpr (valid k (List.mem_range.mp hk)).1,
             (stable_valid frame).mpr (valid k (List.mem_range.mp hk)).2⟩) rest
    refine ⟨?_,stable_trans frame result.2⟩
    simp only [stable_value frame] at result
    have hz : decode ((assign s acc 0).regs acc) = (0 : Float) := by
      simp only [assign,Function.update_self]
      rfl
    rw [hz] at result
    exact result.1

theorem exists_execution (s : State) (allowed : Accumulator acc)
    (valid : ∀ k<width, Valid s width k a ∧ Valid s width k b) :
    ∃ t, Block (program width acc a b) s t := by
  have frame : Stable s (assign s acc 0) := by
    rcases allowed with rfl|rfl <;> exact stable_assign _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t,ht⟩ := terms_exists (assign s acc 0) allowed (by
    intro k hk
    exact ⟨(stable_valid frame).mpr (valid k (List.mem_range.mp hk)).1,
           (stable_valid frame).mpr (valid k (List.mem_range.mp hk)).2⟩)
  exact ⟨t,.cons .mov ht⟩

end PtxTorchLean.Poisson.PTX.Contraction

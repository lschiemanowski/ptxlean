import PtxBinary32.MaximumUniversal
import PtxBinary32.SumCorrect

/-! Reduction launch interfaces for the reference softmax pipeline. Each launch
retains an actual fetched, completed, admitted parallel execution. Exact global
array frames account for the maximum temporarily overwriting the first weight. -/
namespace Ptx.Scalar.Parallel.SoftmaxReductions

theorem maximumBounds (d : Nat) (bound : Sum.Bounds d) : Maximum.Bounds d := by
  simpa [Maximum.Bounds,Sum.shape,Dense.Shape.threads,Dense.Shape.width,Sum.width] using (Sum.denseBounds d bound).threads

/-- The maximum writes only its output cell, even with an arbitrary suffix. -/
theorem maximum_frame (d : Nat) (bound : Maximum.Bounds d) (before shared : List Word)
    (seeds : Fin (Maximum.width d) → Scalar.State)
    {events : List (Event (Maximum.width d))} {final : State (Maximum.width d)}
    (run : Runs (Maximum.config d) (Maximum.program d) (Maximum.initial d before shared seeds) events final)
    (i : Nat) (different : i≠Maximum.width d) : final.global[i]?=before[i]? := by
  have result := Replay.run_value run .global i
  dsimp [Replay.arena,Replay.arrays,Maximum.initial] at result
  cases last : Replay.latestWrite .global i events with
  | none => simpa [last] using result
  | some value =>
    obtain ⟨left,event,right,split,written,_⟩ := Replay.latestWrite_origin .global i events value last
    have member : event∈events := by simp [split]
    obtain ⟨t,occ,address,rfl,memory,atIndex⟩ := Replay.writtenAt_some .global i event value written
    have owner := Maximum.candidate_global_owner d bound before shared seeds run t occ
      ⟨.store,address,value⟩ member memory rfl
    have fit : 4*Maximum.width d<18446744073709551616 := by
      have := Maximum.width_fits bound; omega
    change address.toNat/4=i at atIndex
    have addr : address=Maximum.bytePointer (Maximum.width d) := owner.2.1
    rw [addr] at atIndex
    have idx : Maximum.width d=i := by
      simpa [Maximum.bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] using atIndex
    exact False.elim (different idx.symm)

/-- Completed admitted maximum runs preserve every cell except their output. -/
theorem maximum_exact (d : Nat) (bound : Maximum.Bounds d) (before shared : List Word)
    (seeds : Fin (Maximum.width d) → Scalar.State)
    {events : List (Event (Maximum.width d))} {final : State (Maximum.width d)}
    (run : Runs (Maximum.config d) (Maximum.program d) (Maximum.initial d before shared seeds) events final)
    (halted : ∀t, (final.lanes t).halted=true) (source co)
    (valid : Maximum.Admitted d bound before shared seeds run source co) :
    final.global=before.set (Maximum.width d) (Maximum.node before d 0) := by
  have result := Maximum.completed_maximum d bound before shared seeds run halted source co valid
  have size : Maximum.width d<before.length := by
    obtain ⟨h,_⟩ := List.getElem?_eq_some_iff.mp result.1
    simpa only [result.2.2.1] using h
  apply List.ext_getElem?
  intro i
  by_cases same : i=Maximum.width d
  · subst i
    simpa [size] using result.1
  · rw [maximum_frame d bound before shared seeds run i same]
    exact (List.getElem?_set_ne (Ne.symm same)).symm

/-- A real run, completion and memory admission; no desired output premise. -/
inductive MaximumLaunch (d : Nat) (before : List Word) : List Word → Prop
  | kernel (bound : Sum.Bounds d) (shared : List Word)
      (seeds : Fin (Maximum.width d) → Scalar.State)
      {events : List (Event (Maximum.width d))} {final : State (Maximum.width d)}
      (run : Runs (Maximum.config d) (Maximum.program d) (Maximum.initial d before shared seeds) events final)
      (halted : ∀t, (final.lanes t).halted=true)
      (admitted : ∃source co, Maximum.Admitted d (maximumBounds d bound) before shared seeds run source co) :
      MaximumLaunch d before final.global

theorem maximum_launch_correct (run : MaximumLaunch d before after) :
    after=before.set (Maximum.width d) (Maximum.node before d 0) := by
  cases run with
  | kernel bound shared seeds run halted admitted =>
    obtain ⟨source,co,valid⟩ := admitted
    exact maximum_exact d (maximumBounds d bound) before shared seeds run halted source co valid

/-- The admitted witness uses actual instructions and a proved memory graph. -/
theorem maximum_launch_exists (d : Nat) (bound : Sum.Bounds d) (before : List Word)
    (allocated : Maximum.width d+1≤before.length) : ∃after, MaximumLaunch d before after := by
  let shared := List.replicate (Maximum.sharedWords d) (0 : Word)
  let seeds : Fin (Maximum.width d)→Scalar.State := fun _ => ⟨0,fun _=>0,fun _=>0,fun _=>false,[]⟩
  obtain ⟨events,final,run,source,co,valid,_,_,halted,_,_⟩ :=
    Maximum.selected_admitted (maximumBounds d bound) before shared seeds allocated (by simp [shared])
  exact ⟨final.global,.kernel bound shared seeds run.toRuns halted ⟨source,co,valid⟩⟩

/-- The sum uses the actual dense specialization instruction list. -/
abbrev SumLaunch (d : Nat) (input : Fin (Sum.width d) → Word) : List Word → Prop :=
  Dense.Launch (Sum.shape d) (Sum.global d input)

theorem sum_launch_exists (d : Nat) (bound : Sum.Bounds d) (input : Fin (Sum.width d) → Word) :
    ∃after, SumLaunch d input after :=
  Dense.launch_exists (Sum.shape d) (Sum.global d input) (fun _ => Sum.denseBounds d bound) (by simp)

/-- The fully specified sum arena changes only at its output cell. -/
theorem sum_launch_correct (d : Nat) (input : Fin (Sum.width d) → Word) (run : SumLaunch d input after) :
    ∃out, after=(Sum.global d input).set (Sum.outputIndex d) out ∧ Sum.Output d input out := by
  have result := Dense.launch_correct run
  obtain ⟨out,stored,allowed⟩ := result.1 ⟨0,by simp [Sum.shape]⟩
  have stored' : after[Sum.outputIndex d]?=some out := by simpa using stored
  refine ⟨out,?_,(Sum.output_iff d input out).mp allowed⟩
  have size : (Sum.global d input).length=Sum.outputIndex d+1 := by simp [Sum.outputIndex]
  apply List.ext_getElem?
  intro i
  by_cases same : i=Sum.outputIndex d
  · subst i
    simpa [size] using stored'
  · by_cases below : i<Sum.outputIndex d
    · rw [result.2.1 i (by simpa using below)]
      exact (List.getElem?_set_ne (Ne.symm same)).symm
    · have outside : after.length ≤ i := by rw [result.2.2,size]; omega
      have old : (Sum.global d input).length ≤ i := by rw [size]; omega
      simp [List.getElem?_eq_none_iff.mpr outside,List.getElem?_eq_none_iff.mpr old,
        List.getElem?_set_ne (Ne.symm same)]

/-- The packaged maximum exposes a real safe trace, not an opaque array oracle. -/
theorem maximum_launch_safe (launch : MaximumLaunch d before after) :
    ∃bound : Sum.Bounds d, ∃shared seeds events final,
      ∃run : Runs (Maximum.config d) (Maximum.program d) (Maximum.initial d before shared seeds) events final,
      after=final.global ∧ (∀t, (final.lanes t).halted=true) ∧
      (∃source co, Maximum.Admitted d (maximumBounds d bound) before shared seeds run source co) ∧
      (∀event∈events, AccessSafe (Maximum.initial d before shared seeds) event) := by
  cases launch with
  | kernel bound shared seeds run halted admitted =>
    exact ⟨bound,shared,seeds,_,_,run,rfl,halted,admitted,runs_access_safe run⟩

/-- The sum package similarly exposes the actual safe admitted execution. -/
theorem sum_launch_safe (launch : SumLaunch d input after) :
    ∃bound : Dense.Bounds (Sum.shape d), ∃seeds events final,
      ∃run : Runs (Dense.config (Sum.shape d) bound) (Sum.program d)
        (Sum.initial d input (List.replicate (Sum.sharedWords d) 0) seeds) events final,
      after=final.global ∧ (∀t, (final.lanes t).halted=true) ∧
      (∃source co, Dense.Admitted (Sum.shape d) bound (Sum.global d input)
        (List.replicate (Sum.sharedWords d) 0) seeds run source co) ∧
      (∀event∈events, AccessSafe (Sum.initial d input (List.replicate (Sum.sharedWords d) 0) seeds) event) := by
  rw [← Sum.sharedWords_eq d]
  cases launch with
  | empty zero => simp [Sum.shape] at zero
  | kernel bound seeds run halted admitted =>
    exact ⟨bound,seeds,_,_,run,rfl,halted,admitted,runs_access_safe run⟩

/-- The selected input word is an attained maximum and satisfies each score's
shifted-exponential input contract. This lemma concerns the packed input arena. -/
theorem maximum_input_bounds (d : Nat) (input : Fin (Sum.width d) → Word)
    (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, Ptx.Binary32.finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ)) :
    ∃m, Ptx.Binary32.finiteReal (Maximum.node (Sum.global d input) d 0)=some m ∧
      (∀i, Ptx.Binary32.ShiftedExp.InputBounds (values i) m) ∧
      ∃i, Maximum.node (Sum.global d input) d 0=input i ∧ m=values i := by
  have vf : ∀j, j<2^d → Ptx.Binary32.finiteReal ((Sum.global d input)[j]!)=some (Sum.valuesAt d values j) := by
    intro j hj
    have h : j<Sum.width d := hj
    rw [Sum.global_input_bang d input j h]
    simpa [Sum.valuesAt,List.getElem!_eq_getElem?_getD,h] using finite ⟨j,h⟩
  have vb : ∀j, j<2^d → |Sum.valuesAt d values j|≤(2:ℝ)^(124:ℤ) := by
    intro j hj
    have h : j<Sum.width d := hj
    simpa [Sum.valuesAt,List.getElem!_eq_getElem?_getD,h] using small ⟨j,h⟩
  obtain ⟨m,real,bounds,j,hj,word,val⟩ := Ptx.Binary32.Maximum.Tree.root_shifted_bounds
    (fun j => (Sum.global d input)[j]!) (Sum.valuesAt d values) d vf vb
  have hj' : j<Sum.width d := hj
  refine ⟨m,real,?_,⟨j,hj'⟩,?_,?_⟩
  · intro i
    simpa [Sum.valuesAt,List.getElem!_eq_getElem?_getD,i.isLt] using bounds i.val i.isLt
  · simpa [Maximum.node,Sum.global_input_bang d input j hj',List.getElem!_eq_getElem?_getD,hj'] using word
  · simpa [Sum.valuesAt,List.getElem!_eq_getElem?_getD,hj'] using val

end Ptx.Scalar.Parallel.SoftmaxReductions

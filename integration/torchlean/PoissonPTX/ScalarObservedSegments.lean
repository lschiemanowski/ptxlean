import PoissonPTX.ScalarObservedReplay

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

def noMemory : Instr → Bool
  | .base (.data (.data (.load64 ..))) | .base (.data (.data (.store64 ..))) |
    .base (.data (.load32 ..)) | .store32 .. => false
  | _ => true

theorem no_memory_events (actual : Eval ctx i s t events) (plain : noMemory i=true) : events=[] := by
  cases actual with
  | extra => rfl
  | store32 => simp [noMemory] at plain
  | base actual =>
    cases actual with
    | simple => rfl
    | data actual =>
      cases actual with
      | data actual => cases actual with
        | ordinary => rfl
        | load => simp [noMemory] at plain
        | store => simp [noMemory] at plain
      | mad32 => rfl
      | wide4 => rfl
      | load32 => simp [noMemory] at plain

theorem no_memory_sequence (actual : Sequence ctx code s events t) (plain : ∀ i∈code, noMemory i=true) :
    events=[] ∧ Scalar.Sequence ctx code s t := by
  induction actual with
  | nil => exact ⟨rfl,.nil⟩
  | cons alive step rest ih =>
    have head := no_memory_events step (plain _ (by simp))
    obtain ⟨tail,run⟩ := ih (fun i mem => plain i (by simp [mem]))
    exact ⟨by simp [head,tail],.cons alive (replay step (by simp [ReadValues,head])) run⟩

theorem sequence_append (one : Sequence ctx left s first middle) (two : Sequence ctx right middle rest t) :
    Sequence ctx (left++right) s (first++rest) t := by
  induction one with
  | nil => exact two
  | cons alive step run ih => simpa only [List.append_assoc,List.cons_append] using Sequence.cons alive step (ih two)

theorem sequence_split (left right : List Instr) (actual : Sequence ctx (left++right) s events t) :
    ∃ middle first rest, Sequence ctx left s first middle ∧ Sequence ctx right middle rest t ∧ events=first++rest := by
  induction left generalizing s events with
  | nil => exact ⟨s,[],events,.nil,actual,rfl⟩
  | cons i left ih =>
    cases actual with
    | cons alive step run =>
      obtain ⟨middle,first,rest,one,two,same⟩ := ih run
      exact ⟨middle,_,rest,.cons alive step one,two,by simp [same,List.append_assoc]⟩

theorem sequence_witness (actual : Scalar.Sequence ctx code s t) : ∃ events, Sequence ctx code s events t := by
  induction actual with
  | nil => exact ⟨[],.nil⟩
  | cons alive step rest ih =>
    obtain ⟨events,recorded,_⟩ := eval_witness step
    obtain ⟨tail,run⟩ := ih
    exact ⟨events++tail,.cons alive recorded run⟩

end PtxTorchLean.Poisson.PTX.Scalar.Observed

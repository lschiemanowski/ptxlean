import PoissonPTX.ConcurrentProjection

namespace PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks
open Ptx

def key : Barrier.Key := ⟨0,0,0,3⟩
def write (space : Space) (address : Nat) (value : Word) : Event 1 := .data 0 ⟨space,⟨0,true,address,value⟩⟩
def read (space : Space) (address : Nat) (value : Word) : Event 1 := .data 0 ⟨space,⟨4,false,address,value⟩⟩
def small : List (Event 1) :=
  [write .shared 0 1,.barrier (.arrival key 0),.barrier (.completion key),read .shared 0 1,read .global 8 0]
def large : List (Event 1) :=
  [write .global 256 2,write .shared 0 1,.barrier (.arrival key 0),.barrier (.completion key),
    write .global 264 3,read .shared 0 1,read .global 8 0]

def embedding : Embedding small large where
  position := fun r => if r<3 then r+1 else r+2
  increasing := by intro a b h; dsimp only; split <;> split <;> omega
  fetch := by intro r h; have bound : r<5 := h; interval_cases r <;> rfl

def original (r : Nat) (k : Fin 8) : Sources.Origin Nat := if r=5 then .store 1 k else .initial

theorem whole_compatible : Visibility.Compatible (fun _ _ => 0) large original := by
  intro r reader ra hr load k
  have bound : r<7 := (List.getElem?_eq_some_iff.mp hr).1
  interval_cases r <;> simp [large,write,read] at hr <;> obtain ⟨rfl,rfl⟩ := hr
  all_goals simp_all [original,large,write,read,byte]

theorem whole_performed : Visibility.Performed large original := by
  intro w r writer reader wa ra hw hr store load sw sr order j k same
  have bound : r<7 := (List.getElem?_eq_some_iff.mp hr).1
  interval_cases r <;> simp [large,write,read] at hr <;> obtain ⟨rfl,rfl⟩ := hr
  all_goals simp_all [original]

theorem separated : Separated embedding := by
  apply separated_by_fence (fence:=16) embedding
  · intro r reader ra hr load global
    have bound : r<5 := (List.getElem?_eq_some_iff.mp hr).1
    interval_cases r <;> simp [small,write,read] at hr <;> obtain ⟨rfl,rfl⟩ := hr
    all_goals simp_all
  · intro w writer wa hw store omitted
    have bound : w<7 := (List.getElem?_eq_some_iff.mp hw).1
    interval_cases w <;> simp [large,write,read] at hw <;> obtain ⟨rfl,rfl⟩ := hw
    all_goals try simp_all
    exact False.elim (omitted ⟨0,by decide,rfl⟩)

theorem retained_compatible : Visibility.Compatible (fun _ _ => 0) small (source embedding original) :=
  compatible embedding separated whole_compatible

theorem retained_performed : Visibility.Performed small (source embedding original) :=
  performed embedding whole_performed

/-- The shared read still names its real producer, now at index zero rather than
index one. Removing output stores must not accidentally change that source. -/
theorem renamed_source (k : Fin 8) : source embedding original 3 k=.store 0 k := by
  have inverse : Function.invFun embedding.position 1=0 :=
    Function.leftInverse_invFun embedding.increasing.injective 0
  simpa [source,embedding,original] using congrArg (fun v => Sources.Origin.store v k) inverse

/-- The retained history includes an actual ordered arrival/completion pair. -/
theorem ordered : Visibility.Across small 0 3 :=
  ⟨0,0,⟨.shared,⟨0,true,0,1⟩⟩,⟨.shared,⟨4,false,0,1⟩⟩,key,1,2,
    rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

/-- Overlap by even one byte invalidates erasure; word-start inequality alone
would incorrectly admit this mutation. -/
def overlapping : List (Event 1) := large.set 0 (write .global 15 2)
def badEmbedding : Embedding small overlapping where
  position := embedding.position
  increasing := embedding.increasing
  fetch := by intro r h; have bound : r<5 := h; interval_cases r <;> rfl

theorem overlap_rejected : ¬Separated badEmbedding := by
  intro h
  have omitted : ¬Retained badEmbedding 0 := by
    rintro ⟨v,_,hv⟩
    simp only [badEmbedding,embedding] at hv
    split at hv <;> omega
  exact h 0 0 ⟨.global,⟨0,true,15,2⟩⟩ rfl rfl omitted
    4 0 ⟨.global,⟨4,false,8,0⟩⟩ rfl rfl rfl 0 7 rfl

end PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks

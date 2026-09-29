import PoissonPTX.CellMiddleInputs

/-! A word view built from actual event values. Initial bytes supply global and
plane-zero words; the other shared words come from unique actual stores. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView

def writesAt (address : Nat) : Event n → Bool
  | .data _ access => access.data.store && access.space==.shared && access.data.address==address
  | _ => false

def stored (events : List (Event n)) (address : Nat) : Word :=
  match events.find? (writesAt address) with
  | some (.data _ access) => access.data.value
  | _ => 0

/-- No numerical result is guessed: retrieve the unique executed store record. -/
theorem stored_eq {events : List (Event n)} {w : Nat}
    (observed : events[w]?=some (.data writer wa)) (store : wa.data.store=true) (shared : wa.space=.shared)
    (owner : Visibility.SoleWriter events w wa.data.address) : stored events wa.data.address=wa.data.value := by
  have existsMatch : ∃ event∈events, writesAt wa.data.address event=true :=
    ⟨.data writer wa,List.mem_of_getElem? observed,by simp [writesAt,store,shared]⟩
  obtain ⟨event,found⟩ : ∃ event, events.find? (writesAt wa.data.address)=some event := by
    cases he : events.find? (writesAt wa.data.address) with
    | some event => exact ⟨event,rfl⟩
    | none =>
      have hf := List.find?_eq_none.mp he
      obtain ⟨event,mem,yes⟩ := existsMatch
      have := hf event mem
      simp [yes] at this
  have member := List.mem_of_find?_eq_some found
  have yes := List.find?_some found
  cases event with
  | barrier => simp [writesAt] at yes
  | data thread access =>
    simp only [writesAt,Bool.and_eq_true,beq_iff_eq] at yes
    obtain ⟨⟨write,space⟩,address⟩ := yes
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp member
    have eq : i=w := owner i thread access hi write space 0 0 (by simpa using address)
    subst i
    have ae : access=wa := by have h := Option.some.inj (hi.symm.trans observed); cases h; rfl
    simp [stored,found,ae]

def memory (initial : Space → Memory) (events : List (Event n)) (base width : Nat) : Space → Nat → Word
  | .global,address => read64 (initial .global) address
  | .shared,address => if address<base+width*width*8 then read64 (initial .shared) address else stored events address

theorem global (initial : Space → Memory) (events : List (Event n)) (base width address : Nat) :
    memory initial events base width .global address=read64 (initial .global) address := rfl

theorem input {base width address : Nat} (initial : Space → Memory) (events : List (Event n))
    (inside : address<base+width*width*8) :
    memory initial events base width .shared address=read64 (initial .shared) address := by simp [memory,inside]

theorem output {events : List (Event n)} {w : Nat}
    (observed : events[w]?=some (.data writer wa)) (store : wa.data.store=true) (shared : wa.space=.shared)
    (owner : Visibility.SoleWriter events w wa.data.address)
    (outside : base+width*width*8≤wa.data.address) :
    memory initial events base width .shared wa.data.address=wa.data.value := by
  simp only [memory,show ¬wa.data.address<base+width*width*8 by omega,ite_false]
  exact stored_eq observed store shared owner

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView

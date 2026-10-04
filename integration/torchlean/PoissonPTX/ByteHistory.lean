import PoissonPTX.BarrierSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

/-- A witness-side byte view computed only from actual recorded stores. This
is not an update to any thread state or an alternative memory-admission rule. -/
def applyEvent (memory : Space → Memory) : Event n → Space → Memory
  | .barrier _ => memory
  | .data _ a => if a.data.store then
      Function.update memory a.space (write64 (memory a.space) a.data.address a.data.value)
    else memory

def publish (memory : Space → Memory) : List (Event n) → Space → Memory
  | [] => memory
  | event::rest => publish (applyEvent memory event) rest

def Covers (event : Event n) (space : Space) (address : Nat) : Prop :=
  ∃ owner a, event=.data owner a ∧ a.data.store=true ∧ a.space=space ∧
    a.data.address≤address ∧ address<a.data.address+8

/-- The most recent actual store covering one byte, with its real byte offset.
Byte-wise selection also handles partial overlaps without an atomicity premise. -/
def origin (events : List (Event n)) (space : Space) (address : Nat) : Sources.Origin Nat :=
  match events with
  | [] => .initial
  | event::rest => match origin rest space address with
    | .store w k => .store (w+1) k
    | .initial => match event with
      | .barrier _ => .initial
      | .data _ a => if h : a.data.store=true ∧ a.space=space ∧ a.data.address≤address ∧ address<a.data.address+8
          then .store 0 ⟨address-a.data.address,by omega⟩ else .initial

theorem publish_append (memory : Space → Memory) (left right : List (Event n)) :
    publish memory (left++right)=publish (publish memory left) right := by
  induction left generalizing memory with
  | nil => rfl
  | cons e rest ih => exact ih _

variable {space : Space} {address : Nat}

theorem origin_initial (events : List (Event n)) :
    origin events space address=.initial ↔ ∀ e∈events, ¬Covers e space address := by
  induction events with
  | nil => simp [origin]
  | cons e rest ih =>
    simp only [List.forall_mem_cons, ← ih]
    cases e <;> cases found : origin rest space address <;> simp [origin,found,Covers]

theorem origin_value (events : List (Event n)) (memory : Space → Memory) :
    match origin events space address with
    | .initial => publish memory events space address=memory space address
    | .store w k => ∃ owner a, events[w]?=some (.data owner a) ∧ a.data.store=true ∧ a.space=space ∧
        a.data.address+k.val=address ∧ publish memory events space address=byte a.data.value k.val := by
  induction events generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    have later := ih (applyEvent memory e)
    cases found : origin rest space address with
    | store w k =>
      simp only [found] at later
      obtain ⟨owner,a,atStore,write,same,atByte,value⟩ := later
      simp only [origin,found,publish]
      exact ⟨owner,a,by simpa using atStore,write,same,atByte,value⟩
    | initial =>
      simp only [found] at later
      cases e with
      | barrier b => simpa only [origin,found,publish,applyEvent] using later
      | data owner a =>
        simp only [origin,found]
        by_cases hit : a.data.store=true ∧ a.space=space ∧ a.data.address≤address ∧ address<a.data.address+8
        · simp only [dite_eq_left hit]
          refine ⟨owner,a,by simp,hit.1,hit.2.1,by omega,?_⟩
          change publish (applyEvent memory (.data owner a)) rest space address=_
          rw [later]
          simp [applyEvent,hit.1,hit.2.1,write64,hit.2.2.1,hit.2.2.2]
        · simp only [dite_eq_right hit]
          change publish (applyEvent memory (.data owner a)) rest space address=memory space address
          rw [later]
          by_cases write : a.data.store=true
          · by_cases same : a.space=space
            · have outside : ¬(a.data.address≤address ∧ address<a.data.address+8) := by
                intro hit; exact ‹¬(a.data.store=true ∧ a.space=space ∧ a.data.address≤address ∧ address<a.data.address+8)› ⟨write,same,hit⟩
              simp [applyEvent,write,same,write64,outside]
            · simp [applyEvent,write,Function.update_of_ne (Ne.symm same)]
          · simp [applyEvent,write]

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

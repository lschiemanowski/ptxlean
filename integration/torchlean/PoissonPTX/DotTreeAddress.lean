import PoissonPTX.DotTreeControl

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Address tracking needs only the data instructions. Comparisons, branches
and barriers clear the scratch-address fact in this syntactic scan. -/
def addressCode : List Instr := Reduction.Native.code.map fun i => match i with
  | .data op => .data op
  | _ => .sync 0

def treeAddressTag (pc : Nat) : Address.Tag :=
  if 20≤pc ∧ pc<96 then AddressHold.tag addressCode (pc-20) else .none

def TreeAddress (s : Flow.State) : Prop := Address.Ready (treeAddressTag s.core.pc) s.core

theorem tree_address_outside (early : s.core.pc≤20 ∨ 96≤s.core.pc) : TreeAddress s := by
  rcases early with early | late
  · by_cases same : s.core.pc=20
    · simp [TreeAddress,treeAddressTag,same,AddressHold.tag_zero,Address.Ready]
    · have outside : ¬20≤s.core.pc := by omega
      simp [TreeAddress,treeAddressTag,outside,Address.Ready]
  · have outside : ¬s.core.pc<96 := by omega
    simp [TreeAddress,treeAddressTag,outside,Address.Ready]

theorem checked_tree_address : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data op) => decide (treeAddressTag (21+slot.val)=AddressHold.nextTag (treeAddressTag (20+slot.val)) (.data op))
    | some (.branch target) => decide (treeAddressTag (21+slot.val)=.none ∧ treeAddressTag (20+target)=.none)
    | _ => decide (treeAddressTag (21+slot.val)=.none))=true := by decide +kernel

theorem tree_address_native
    (fetch : Reduction.Native.code[slot]?=some native) (ordinary : treeInstruction native=.flow i)
    (pc : s.core.pc=20+slot) (actual : Flow.Observed.Eval ctx i s t access index)
    (ready : TreeAddress s) : TreeAddress t := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [Reduction.Native.length] at bound
  have checked := checked_tree_address ⟨slot,bound⟩
  rw [fetch] at checked
  have stable := tree_keeps_setup fetch ordinary
  cases native <;> cases ordinary
  · simp only [decide_eq_true_eq] at checked
    cases actual with
    | data step =>
      cases step with
      | data step =>
        change Address.Ready (treeAddressTag _) _
        rw [data_pc step,pc,show 20+slot+1=21+slot by omega,checked]
        exact AddressHold.data_ready step (by simpa only [TreeAddress,pc] using ready) stable.1 stable.2
    | simple ordinary => exact False.elim (ordinary _ rfl)
  · simp only [decide_eq_true_eq] at checked
    cases actual
    change Address.Ready (treeAddressTag (s.core.pc+1)) _
    rw [pc,show 20+slot+1=21+slot by omega,checked]
    trivial
  · simp only [decide_eq_true_eq] at checked
    cases actual
    change TreeAddress (if s.predicates 0=true then _ else _)
    split
    · change Address.Ready (treeAddressTag _) _
      simp only [Flow.goto]
      rw [checked.2]; trivial
    · change Address.Ready (treeAddressTag (s.core.pc+1)) _
      rw [pc,show 20+slot+1=21+slot by omega,checked.1]; trivial

theorem tree_address_flow
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index) (ready : TreeAddress s) : TreeAddress t := by
  by_cases input : s.core.pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    exact tree_address_outside (Or.inl (NativeFlow.eval_upper actual input (input_syntax (List.mem_of_getElem? found)).1))
  · by_cases inside : s.core.pc<96
    · have position : s.core.pc=20+(s.core.pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      exact tree_address_native found equal position actual ready
    · apply tree_address_outside (Or.inr (NativeFlow.eval_lower actual (by omega) ?_))
      have position : s.core.pc=96+(s.core.pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

theorem tree_address_sync
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.sync resource)) :
    TreeAddress (Flow.next s) := by
  have lower : 20≤s.core.pc := by
    by_contra h
    exact no_early_sync (by omega) fetch
  have upper : s.core.pc<96 := by
    by_contra h
    have position : s.core.pc=96+(s.core.pc-96) := by omega
    rw [position,tail_fetch] at fetch
    cases (tail output)[s.core.pc-96]? <;> simp at fetch
  have position : s.core.pc=20+(s.core.pc-20) := by omega
  rw [position,tree_fetch (by omega)] at fetch
  obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
  have checked := checked_tree_address ⟨s.core.pc-20,by omega⟩
  rw [found] at checked
  cases op <;> cases equal
  simp only [decide_eq_true_eq] at checked
  change Address.Ready (treeAddressTag (s.core.pc+1)) _
  rw [show s.core.pc+1=21+(s.core.pc-20) by omega,checked]
  trivial

theorem tree_addresses
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0) :
    ∀ owner, TreeAddress (NativeFlow.lane final owner) := by
  apply NativeFlow.runs_lanes (P:=fun _ s => TreeAddress s) run aligned
    (fun owner => tree_address_outside (Or.inl (by simp [NativeFlow.lane,entry])))
  · intro owner i before after access index ready fetch actual
    exact tree_address_flow fetch actual ready
  · intro owner before resource _ fetch
    exact tree_address_sync fetch

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

import PoissonPTX.ReductionPublication

/-! Source selection for every read position of the 256-lane shared tree.
Actual control and address invariants discharge the structural premises of
the generic stage-source lemmas. Numerical tree composition is separate. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control
open Visibility.Repeated

def previous (k : Fin 8) : Fin 9 := ⟨k.val,by omega⟩
def current (k : Fin 8) : Fin 9 := ⟨k.val+1,by omega⟩
def readPC (k : Fin 8) (right : Bool) : Nat := (if right then 8 else 7)+8*k.val
def readOffset (k : Fin 8) (right : Bool) : Word :=
  BitVec.ofNat 64 (if right then active (current k)*8 else 0)
def readAddress (k : Fin 8) (right : Bool) : Operand :=
  if right then .offset 2 (readOffset k true) else .reg 2

theorem checked_reads : ∀ (k : Fin 8) (right : Bool),
    program[readPC k right]?=some (.data (.load64 .shared (if right then 5 else 4) (readAddress k right))) ∧
    AddressHold.tag program (readPC k right)=.addressed ∧
    limit (readPC k right)=active (current k) := by decide +kernel

theorem ranges : ∀ k : Fin 8,
    active (previous k)=2*active (current k) ∧ active (previous k)≤256 ∧
    active (current k)≤128 := by decide +kernel

/-- Identify the actual load address from preserved registers and fetched
address preparation, for either side of an active pair. -/
theorem read_geometry {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64) (k : Fin 8) (right : Bool)
    (member : Event.data thread access∈events) (pc : access.data.pc=readPC k right) :
    access.data.store=false ∧ access.space=.shared ∧ thread.val<active (current k) ∧
    access.data.address=base+(thread.val+(if right then active (current k) else 0))*8 := by
  have inv : Limits.Invariant limit start := by intro t; rw [entry]; exact t.isLt
  have live := Limits.access_active run aligned inv boundaries member
  rw [pc,(checked_reads k right).2.2] at live
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have location := access_pc hd
  have atRead : (before.lanes thread).pc=readPC k right := location.symm.trans pc
  have prepared : AddressHold.Invariant program start := by
    intro t; rw [entry,AddressHold.tag_zero]; trivial
  have ready := AddressHold.runs_invariant hp aligned prepared entries frames.1 frames.2 thread
  rw [atRead,(checked_reads k right).2.1] at ready
  change (before.lanes thread).regs 2=(before.lanes thread).regs 3+wide (before.lanes thread) 14 at ready
  have baseEq : ((before.lanes thread).regs 3).toNat=base := by
    rw [Address.runs_keeps hp frames.1]; exact baseReg thread
  have laneEq : ((before.lanes thread).regs 14).toNat=thread.val := by
    rw [Address.runs_keeps hp frames.2]; exact laneReg thread
  have offset : (readOffset k right).toNat=(if right then active (current k)*8 else 0) := by
    unfold readOffset
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have bound := (ranges k).2.2
    split <;> omega
  have address := SharedStore.location_exact (before.lanes thread) (readOffset k right)
    (by rw [laneEq]; have := thread.isLt; omega)
    (by rw [baseEq,laneEq,offset]; have bound := ranges k; split <;> omega)
  rw [atRead,(checked_reads k right).1] at fetch
  cases fetch
  cases hd with
  | load =>
    refine ⟨rfl,rfl,live,?_⟩
    simp only [SharedStore.location,baseEq,laneEq,offset] at address
    cases right <;> simp [readAddress,readOffset,Operand.eval,ready] at address ⊢
    · exact address
    · simpa only [Nat.add_mul,Nat.add_assoc] using address

/-- The program has no other loads: every read belongs to an active pair. -/
theorem checked_read_sites : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data (.load64 _ _ _)) =>
      decide (∃ (k : Fin 8) (right : Bool), pc.val=readPC k right)
    | _ => true)=true := by decide +kernel

theorem read_coverage (run : Runs cfg program start events final)
    (member : Event.data thread access∈events) (read : access.data.store=false) :
    ∃ (k : Fin 8) (right : Bool), access.data.pc=readPC k right := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  cases hd with
  | load =>
    have h := checked_read_sites ⟨_,by
      have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
    simpa only [fetch,decide_eq_true_eq] using h
  | store => cases read

/-- For either operand, recover its previous-stage producer and all source
bytes from the actual execution. No producer, address or barrier premise is
supplied by the caller. This is conditional on the explicit admission rules. -/
theorem selected_read {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (k : Fin 8) (right : Bool) (observed : events[r]?=some (.data thread access))
    (pc : access.data.pc=readPC k right) :
    ∃ (w : Nat) (owner : Fin 256) (wa : Access), owner.val=thread.val+(if right then active (current k) else 0) ∧
      events[w]?=some (.data owner wa) ∧ wa.data.pc=site (previous k) ∧
      wa.data.store=true ∧ wa.space=.shared ∧ access.data.value=wa.data.value ∧
      ∀ byte, source r byte=.store w byte := by
  have aligned : Aligned start := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨read,shared,live,address⟩ := read_geometry run aligned entry baseReg laneReg noWrap k right
    (List.mem_of_getElem? observed) pc
  have bounds := ranges k
  let owner : Fin 256 := ⟨thread.val+(if right then active (current k) else 0),by split <;> omega⟩
  have ownerLive : owner.val<active (previous k) := by dsimp [owner]; split <;> omega
  have later : site (previous k)+1<access.data.pc := by
    rw [pc]; dsimp [site,previous,readPC]; split <;> omega
  obtain ⟨w,wa,found,position,write,space,across⟩ := published run reset entry (previous k) owner ownerLive observed later
  have stores := stage_stores run aligned entry baseReg laneReg noWrap
  refine ⟨w,owner,wa,rfl,found,position,write,space,?_⟩
  cases right with
  | false =>
    have ownerEq : owner=thread := by apply Fin.ext; simp [owner]
    subst owner
    exact stage_own_read run forward stores sites compatible ordered k found observed write read space shared
      (by simpa using address) position (by omega)
      (by rw [pc]; dsimp [readPC,site]; omega)
  | true =>
    exact stage_neighbor_read run forward stores sites compatible ordered k found observed write read space shared
      address position (by change active (current k)≤thread.val+active (current k); omega) across

/-- Every read in the fragment selects its lane's or neighbor's immediately
preceding tree publication, including all eight byte-source identities. -/
theorem every_read {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (observed : events[r]?=some (.data thread access)) (read : access.data.store=false) :
    ∃ (k : Fin 8) (right : Bool) (w : Nat) (owner : Fin 256) (wa : Access),
      access.data.pc=readPC k right ∧
      owner.val=thread.val+(if right then active (current k) else 0) ∧
      events[w]?=some (.data owner wa) ∧ wa.data.pc=site (previous k) ∧
      wa.data.store=true ∧ wa.space=.shared ∧ access.data.value=wa.data.value ∧
      ∀ byte, source r byte=.store w byte := by
  obtain ⟨k,right,pc⟩ := read_coverage run (List.mem_of_getElem? observed) read
  obtain ⟨w,owner,wa,props⟩ := selected_read run reset entry baseReg laneReg noWrap compatible ordered k right observed pc
  exact ⟨k,right,w,owner,wa,pc,props⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

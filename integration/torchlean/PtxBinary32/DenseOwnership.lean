import PtxBinary32.DenseAddressControl
import PtxBinary32.ParallelStoreControl

/-! Ownership of actual emitted stores in arbitrary candidate forward runs.
No selected load values, memory admission or completed execution is assumed. -/
namespace Ptx.Scalar.Parallel.Dense

/-- Exact byte addresses and the output row-leader condition follow from
fetched instructions, including the predicate of an actually emitted store. -/
theorem candidate_store_address (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    (occ.pc=20 ∧ space=.shared ∧ effect.address=bytePointer t.val) ∨
    (∃ k, k<s.depth ∧ occ.pc=22+16*k+14 ∧ space=.shared ∧ effect.address=bytePointer (nextIndex s k t)) ∨
    (occ.pc=22+16*s.depth+18 ∧ space=.global ∧ effect.address=bytePointer (outputIndex s t) ∧ t.val%s.width=0) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program s)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨address,value,op,addr,gate⟩ := AddressControl.run_store run (program_address_compatible s)
    (initial_address_control s global shared seeds) (reset_aligned _ _ _ _) member memory store
  have fetch := conditions.1
  rcases trace_store_site s run t space occ effect member memory store with ⟨site,rfl⟩ | ⟨k,hk,site,rfl⟩ | ⟨site,rfl⟩
  · have instr : occ.instruction=Scalar.Instr.plain (.store (.reg 2) (.reg 6)) := by
      simpa [site,program,products,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inl ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,product_control_address s b seeds t] using addr⟩
  · rw [site,round_fetch s k hk 14 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 2) (.reg 6)⟩ := by
      simpa [round,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inr (.inl ⟨k,hk,site,rfl,by simpa [Scalar.Operand64.eval,site,round_control_address s b seeds t k hk] using addr⟩)
  · rw [site,output_fetch s 18 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 6) (.reg 6)⟩ := by
      simpa [output,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    have control := output_control_address s b seeds t
    have leader := gate (by rw [instr])
    rw [site,control.2] at leader
    exact .inr (.inr ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,control.1] using addr,by simpa using leader⟩)

/-- A scratch plane is reserved for one stage; each thread owns one word in it. -/
def sharedStorePC (phase : Nat) : Nat := if phase=0 then 20 else 22+16*(phase-1)+14

theorem candidate_shared_owner (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .shared) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    ∃ phase, phase≤s.depth ∧ occ.pc=sharedStorePC phase ∧ effect.address=bytePointer (phase*s.threads+t.val) := by
  rcases candidate_store_address s b global shared seeds run t .shared occ effect member memory store with h | h | h
  · exact ⟨0,Nat.zero_le _,by simpa [sharedStorePC] using h.1,by simpa using h.2.2⟩
  · obtain ⟨k,hk,pc,_,addr⟩ := h
    exact ⟨k+1,hk,by simpa [sharedStorePC] using pc,by simpa [nextIndex,Nat.add_comm] using addr⟩
  · cases h.2.1

theorem candidate_global_owner (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .global) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    occ.pc=22+16*s.depth+18 ∧ effect.address=bytePointer (outputIndex s t) ∧ t.val%s.width=0 := by
  rcases candidate_store_address s b global shared seeds run t .global occ effect member memory store with h | h | h
  · cases h.2.1
  · obtain ⟨_,_,_,h,_⟩ := h; cases h
  · exact ⟨h.1,h.2.2⟩

private theorem pointer_word (i : Nat) (fit : i<2^32) (space : Space) :
    (Memory.location space (bytePointer i)).word=i := by
  have bound : 4*i<18446744073709551616 := by omega
  simp [Memory.location,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]

private theorem same_pointer_index (i j : Nat) (hi : i<2^32) (hj : j<2^32) (space : Space)
    (same : (Memory.location space (bytePointer i)).code=(Memory.location space (bytePointer j)).code) : i=j := by
  have eq := congrArg Ptx.TraceMemory.Location.word (Ptx.TraceMemory.Location.code_injective same)
  simpa [pointer_word i hi space,pointer_word j hj space] using eq

private theorem scratch_index_fits (s : Shape) (b : Bounds s) (t : Fin s.threads) (p : Nat) (hp : p≤s.depth) :
    p*s.threads+t.val<2^32 := by
  have ht := t.isLt
  have mul := Nat.mul_le_mul_right s.threads hp
  have bound := b.arithmetic
  dsimp [Shape.sharedWords] at bound
  rw [Nat.add_mul] at bound
  omega

/-- Two actual stores to one shared location are the same trace event. Fresh
planes identify the stage, and its word offset identifies the issuing thread. -/
theorem shared_store_unique (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (p q : Nat) (t u : Fin s.threads) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some .shared) e)) (hq : events[q]?=some (.scalar u (some .shared) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location .shared a.address).code=(Memory.location .shared z.address).code) : p=q := by
  obtain ⟨i,hi,pc,addr⟩ := candidate_shared_owner s b global shared seeds run t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨j,hj,qc,bddr⟩ := candidate_shared_owner s b global shared seeds run u f z (List.mem_of_getElem? hq) hf hz
  rw [addr,bddr] at same
  have indices := same_pointer_index _ _ (scratch_index_fits s b t i hi) (scratch_index_fits s b u j hj) .shared same
  have pos : 0<s.threads := lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have owner := congrArg (· % s.threads) indices
  simp [Nat.add_mod,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt u.isLt] at owner
  have tid : t=u := Fin.ext owner
  subst u
  have phase : i=j := Nat.mul_right_cancel pos (by omega)
  exact scalar_site_unique s run p q t _ _ e f hp hq (by rw [pc,qc,phase])

/-- Equal output locations have the same row, and emitted output stores must
come from that row's column-zero thread. -/
theorem global_store_unique (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (p q : Nat) (t u : Fin s.threads) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some .global) e)) (hq : events[q]?=some (.scalar u (some .global) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location .global a.address).code=(Memory.location .global z.address).code) : p=q := by
  obtain ⟨pc,addr,leader⟩ := candidate_global_owner s b global shared seeds run t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨qc,bddr,other⟩ := candidate_global_owner s b global shared seeds run u f z (List.mem_of_getElem? hq) hf hz
  rw [addr,bddr] at same
  have fits (v : Fin s.threads) : outputIndex s v<2^32 := by
    have := (output_indices s v).2.2; have := b.arithmetic; omega
  have indices := same_pointer_index _ _ (fits t) (fits u) .global same
  have row : t.val/s.width=u.val/s.width := by unfold outputIndex at indices; omega
  have coords := (coordinates s t).2.2
  have coords' := (coordinates s u).2.2
  have tid : t=u := Fin.ext (by rw [leader] at coords; rw [other,← row] at coords'; omega)
  subst u
  exact scalar_site_unique s run p q t _ _ e f hp hq (by omega)

/-- Includes memory-space separation, rather than relying on numeric pointers
alone to distinguish global and shared locations. -/
theorem candidate_store_unique (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (p q : Nat) (t u : Fin s.threads) (space seen : Space) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some space) e)) (hq : events[q]?=some (.scalar u (some seen) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location space a.address).code=(Memory.location seen z.address).code) : p=q := by
  cases space <;> cases seen
  · exact global_store_unique s b global shared seeds run p q t u e f a z hp hq he hf ha hz same
  · exact False.elim (Memory.spaces_distinct _ _ same)
  · exact False.elim (Memory.spaces_distinct _ _ same.symm)
  · exact shared_store_unique s b global shared seeds run p q t u e f a z hp hq he hf ha hz same

/-- At most one noninitial write to each location in the exact memory graph.
This holds for arbitrary source and coherence choices, even before admission. -/
theorem graph_writer_unique (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (source co) (v w : Fin (Memory.labels (program s) global shared events).length)
    (hv : (Memory.graph (program s) global shared events source co).write v)
    (hw : (Memory.graph (program s) global shared events source co).write w)
    (nv : ¬(Memory.graph (program s) global shared events source co).initial v)
    (nw : ¬(Memory.graph (program s) global shared events source co).initial w)
    (same : (Memory.graph (program s) global shared events source co).sameAddress v w) : v=w := by
  obtain ⟨t,p,space,e,a,hp,_,_,he,ha,ve⟩ := Memory.program_write_origin (program s) global shared events source co v hv nv
  obtain ⟨u,q,seen,f,z,hq,_,_,hf,hz,we⟩ := Memory.program_write_origin (program s) global shared events source co w hw nw
  have location : (Memory.location space a.address).code=(Memory.location seen z.address).code := by
    simpa [Graph.sameAddress,ve,we,Ptx.TraceMemory.Access.effect,Memory.ofEffect] using same
  have position := candidate_store_unique s b global shared seeds run p q t u space seen e f a z hp hq he hf ha hz location
  have owner : t=u := by
    rw [← position,hp] at hq
    exact (Event.scalar.inj (Option.some.inj hq)).1
  have eq : Ptx.TraceMemory.identity ((Memory.graph (program s) global shared events source co).event v)=
      Ptx.TraceMemory.identity ((Memory.graph (program s) global shared events source co).event w) := by
    simp [ve,we,Ptx.TraceMemory.identity,position,owner]
  apply Fin.ext
  apply (Memory.labels_unique (program s) global shared events).eq_of_getElem_eq (by simp) (by simp)
  simpa [Memory.graph,Ptx.TraceMemory.graph] using eq

end Ptx.Scalar.Parallel.Dense

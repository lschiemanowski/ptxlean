import PtxBinary32.MaximumAddressControl
import PtxBinary32.ParallelStoreControl

/-! Ownership of actual emitted stores in arbitrary candidate forward runs.
No selected load values, memory admission or completed execution is assumed. -/
namespace Ptx.Scalar.Parallel.Maximum

/-- Exact byte addresses and the thread-zero output condition follow from
fetched instructions, including the predicate of an actually emitted store. -/
theorem candidate_store_address (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    (occ.pc=4 ∧ space=.shared ∧ effect.address=bytePointer t.val) ∨
    (∃ k, k<d ∧ occ.pc=6+24*k+22 ∧ space=.shared ∧ effect.address=bytePointer (((k+1)*width d+t.val))) ∨
    (occ.pc=6+24*d+10 ∧ space=.global ∧ effect.address=bytePointer (width d) ∧ t.val=0) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program d)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨address,value,op,addr,gate⟩ := AddressControl.run_store run (program_address_compatible d)
    (initial_address_control d global shared seeds) (reset_aligned _ _ _ _) member memory store
  have fetch := conditions.1
  rcases trace_store_site d run t space occ effect member memory store with ⟨site,rfl⟩ | ⟨k,hk,site,rfl⟩ | ⟨site,rfl⟩
  · have instr : occ.instruction=Scalar.Instr.plain (.store (.reg 0) (.reg 4)) := by
      simpa [site,program,publish,publishCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inl ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,publication_control_address b seeds t] using addr⟩
  · rw [site,round_fetch d k hk 22 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 3) (.reg 6)⟩ := by
      simpa [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inr (.inl ⟨k,hk,site,rfl,by simpa [Scalar.Operand64.eval,site,round_control_address b seeds t k hk] using addr⟩)
  · rw [site,output_fetch d 10 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 1) (.reg 6)⟩ := by
      simpa [output,outputCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    have control := output_control_address b seeds t
    have leader := gate (by rw [instr])
    rw [site,control.2] at leader
    exact .inr (.inr ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,control.1] using addr,by simpa using leader⟩)

/-- A scratch plane is reserved for one stage; each thread owns one word in it. -/
def sharedStorePC (phase : Nat) : Nat := if phase=0 then 4 else 6+24*(phase-1)+22

theorem candidate_shared_owner (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .shared) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    ∃ phase, phase≤d ∧ occ.pc=sharedStorePC phase ∧ effect.address=bytePointer (phase*(width d)+t.val) := by
  rcases candidate_store_address d b global shared seeds run t .shared occ effect member memory store with h | h | h
  · exact ⟨0,Nat.zero_le _,by simpa [sharedStorePC] using h.1,by simpa using h.2.2⟩
  · obtain ⟨k,hk,pc,_,addr⟩ := h
    exact ⟨k+1,hk,by simpa [sharedStorePC] using pc,by simpa [Nat.add_comm] using addr⟩
  · cases h.2.1

theorem candidate_global_owner (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .global) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    occ.pc=6+24*d+10 ∧ effect.address=bytePointer (width d) ∧ t.val=0 := by
  rcases candidate_store_address d b global shared seeds run t .global occ effect member memory store with h | h | h
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

private theorem scratch_index_fits (d : Nat) (b : Bounds d) (t : Fin (width d)) (p : Nat) (hp : p≤d) :
    p*(width d)+t.val<2^32 := by
  exact lt_trans (plane_bound d p t.val hp t.isLt) (shared_fits b)

/-- Two actual stores to one shared location are the same trace event. Fresh
planes identify the stage, and its word offset identifies the issuing thread. -/
theorem shared_store_unique (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (p q : Nat) (t u : Fin (width d)) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some .shared) e)) (hq : events[q]?=some (.scalar u (some .shared) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location .shared a.address).code=(Memory.location .shared z.address).code) : p=q := by
  obtain ⟨i,hi,pc,addr⟩ := candidate_shared_owner d b global shared seeds run t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨j,hj,qc,bddr⟩ := candidate_shared_owner d b global shared seeds run u f z (List.mem_of_getElem? hq) hf hz
  rw [addr,bddr] at same
  have indices := same_pointer_index _ _ (scratch_index_fits d b t i hi) (scratch_index_fits d b u j hj) .shared same
  have pos : 0<(width d) := lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have owner := congrArg (· % (width d)) indices
  simp [Nat.add_mod,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt u.isLt] at owner
  have tid : t=u := Fin.ext owner
  subst u
  have phase : i=j := Nat.mul_right_cancel pos (by omega)
  exact scalar_site_unique d run p q t _ _ e f hp hq (by rw [pc,qc,phase])

/-- The output has a single owner: only thread zero emits a global store. -/
theorem global_store_unique (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (p q : Nat) (t u : Fin (width d)) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some .global) e)) (hq : events[q]?=some (.scalar u (some .global) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location .global a.address).code=(Memory.location .global z.address).code) : p=q := by
  obtain ⟨pc,addr,leader⟩ := candidate_global_owner d b global shared seeds run t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨qc,bddr,other⟩ := candidate_global_owner d b global shared seeds run u f z (List.mem_of_getElem? hq) hf hz
  have tid : t=u := Fin.ext (by omega)
  subst u
  exact scalar_site_unique d run p q t _ _ e f hp hq (by omega)

/-- Includes memory-space separation, rather than relying on numeric pointers
alone to distinguish global and shared locations. -/
theorem candidate_store_unique (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (p q : Nat) (t u : Fin (width d)) (space seen : Space) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (.scalar t (some space) e)) (hq : events[q]?=some (.scalar u (some seen) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Memory.location space a.address).code=(Memory.location seen z.address).code) : p=q := by
  cases space <;> cases seen
  · exact global_store_unique d b global shared seeds run p q t u e f a z hp hq he hf ha hz same
  · exact False.elim (Memory.spaces_distinct _ _ same)
  · exact False.elim (Memory.spaces_distinct _ _ same.symm)
  · exact shared_store_unique d b global shared seeds run p q t u e f a z hp hq he hf ha hz same

/-- At most one noninitial write to each location in the exact memory graph.
This holds for arbitrary source and coherence choices, even before admission. -/
theorem graph_writer_unique (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (source co) (v w : Fin (Memory.labels (program d) global shared events).length)
    (hv : (Memory.graph (program d) global shared events source co).write v)
    (hw : (Memory.graph (program d) global shared events source co).write w)
    (nv : ¬(Memory.graph (program d) global shared events source co).initial v)
    (nw : ¬(Memory.graph (program d) global shared events source co).initial w)
    (same : (Memory.graph (program d) global shared events source co).sameAddress v w) : v=w := by
  obtain ⟨t,p,space,e,a,hp,_,_,he,ha,ve⟩ := Memory.program_write_origin (program d) global shared events source co v hv nv
  obtain ⟨u,q,seen,f,z,hq,_,_,hf,hz,we⟩ := Memory.program_write_origin (program d) global shared events source co w hw nw
  have location : (Memory.location space a.address).code=(Memory.location seen z.address).code := by
    simpa [Graph.sameAddress,ve,we,Ptx.TraceMemory.Access.effect,Memory.ofEffect] using same
  have position := candidate_store_unique d b global shared seeds run p q t u space seen e f a z hp hq he hf ha hz location
  have owner : t=u := by
    rw [← position,hp] at hq
    exact (Event.scalar.inj (Option.some.inj hq)).1
  have eq : Ptx.TraceMemory.identity ((Memory.graph (program d) global shared events source co).event v)=
      Ptx.TraceMemory.identity ((Memory.graph (program d) global shared events source co).event w) := by
    simp [ve,we,Ptx.TraceMemory.identity,position,owner]
  apply Fin.ext
  apply (Memory.labels_unique (program d) global shared events).eq_of_getElem_eq (by simp) (by simp)
  simpa [Memory.graph,Ptx.TraceMemory.graph] using eq

end Ptx.Scalar.Parallel.Maximum

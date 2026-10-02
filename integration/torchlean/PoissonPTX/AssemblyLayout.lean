import PoissonPTX.AssemblyExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- The two read-only arrays used by a node's contribution traversal.
Every stored index must identify an allocated cell value. -/
structure Layout (s : State) (entries element : Word) where
  entryCount : Nat
  elementCount : Nat
  base : (s.regs 0).toNat=s.globalStart
  aligned : s.globalStart%8=0
  entriesAligned : entries.toNat%4=0
  elementAligned : element.toNat%8=0
  endBound : limit s≤entryCount
  small : entryCount<2^32
  entriesFit : entries.toNat+entryCount*4≤s.globalBytes
  elementFit : element.toNat+elementCount*8≤s.globalBytes
  noWrap : s.globalStart+s.globalBytes≤2^64
  indices : ∀ k<entryCount,
    (read32 s.global (s.globalStart+entries.toNat+k*4)).toNat<elementCount

theorem valid_of_layout (layout : Layout s entries element) (k : Nat) (inside : k<limit s) :
    Valid (atCursor s k) entries element := by
  have entryBound : k<layout.entryCount := lt_of_lt_of_le inside layout.endBound
  have small : k<2^32 := lt_trans entryBound layout.small
  have wide : k<2^64 := by omega
  have current : Kernel.u32 ((atCursor s k).regs 19)=BitVec.ofNat 32 k := by
    simp [atCursor,Kernel.u32]
  have idxAddress : (indexAddress (atCursor s k) entries).toNat=s.globalStart+entries.toNat+k*4 := by
    unfold indexAddress
    rw [current]
    change (address32 (s.regs 0) (BitVec.ofNat 32 k) entries).toNat=_
    rw [address32_exact _ _ _ (by
      rw [layout.base,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
      have := layout.entriesFit; have := layout.noWrap; omega)]
    rw [layout.base,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    omega
  have indexBound : (index (atCursor s k) entries).toNat<layout.elementCount := by
    unfold index; rw [idxAddress]; exact layout.indices k entryBound
  have valAddress : (valueAddress (atCursor s k) entries element).toNat=
      s.globalStart+element.toNat+(index (atCursor s k) entries).toNat*8 := by
    unfold valueAddress
    change (address64 (s.regs 0) (index (atCursor s k) entries) element).toNat=_
    rw [address64_exact _ _ _ (by
      rw [layout.base]; have := layout.elementFit; have := layout.noWrap; omega),layout.base]
    omega
  constructor
  · change Valid32 s.globalStart s.globalBytes _
    rw [idxAddress]
    refine ⟨by omega,?_,by have := layout.entriesFit; omega,layout.noWrap⟩
    have aligned : s.globalStart%4=0 := by have := layout.aligned; omega
    simp [Nat.add_mod,aligned,layout.entriesAligned]
  · change Valid64 s.globalStart s.globalBytes _
    rw [valAddress]
    refine ⟨by omega,?_,by have := layout.elementFit; omega,layout.noWrap⟩
    simp [Nat.add_mod,layout.aligned,layout.elementAligned]

/-- Physical layouts discharge every access premise in the general loop result. -/
theorem layout_correct
    (run : Flow.Runs ctx (Flow.Loop.program 19 20 (body entries element)) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (within : cursor s.core≤limit s.core) (layout : Layout s.core entries element) :
    decode (t.core.regs 8)=(List.range' (cursor s.core) (limit s.core-cursor s.core)).foldl
      (fun acc k => acc+contribution s.core entries element k) (decode (s.core.regs 8)) :=
  fetched_correct run pc running done within (valid_of_layout layout)

theorem layout_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (within : cursor s.core≤limit s.core) (layout : Layout s.core entries element) :
    ∃ t, Flow.Runs ctx (Flow.Loop.program 19 20 (body entries element)) s t ∧ t.halted=true := by
  obtain ⟨t,run,done,_⟩ := fetched_exists (ctx:=ctx) s pc running within (valid_of_layout layout)
  exact ⟨t,run,done⟩

end PtxTorchLean.Poisson.PTX.Assembly

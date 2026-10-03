import PoissonPTX.ReductionWitnessWords
import PoissonPTX.ConcurrentSerialLanes

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

/-- Physical input conditions sufficient for every own and neighbor access. -/
def Frame (base : Nat) (thread : Fin 256) (s : PTX.State) : Prop :=
  (s.regs 3).toNat=base ∧ (s.regs 14).toNat=thread.val ∧ s.sharedStart=base ∧
    2048≤s.sharedBytes ∧ base+s.sharedBytes≤2^64

theorem frame_advance (frame : Frame base thread s) : Frame base thread (advance s) := frame

theorem frame_initial (frame : Frame base thread s) : Frame base thread (SharedStore.finish s 0 8) := by
  simpa [Frame,SharedStore.finish,put,assign,advance] using frame

theorem frame_update (frame : Frame base thread s) : Frame base thread (finish s left right) := by
  simpa [Frame,finish,loaded,prepared,put,assign,advance] using frame

theorem initial_valid (frame : Frame base thread s) (aligned : base%8=0) : SharedStore.Valid s 0 := by
  obtain ⟨rb,rt,start,room,noWrap⟩ := frame
  have address := SharedStore.location_exact s 0 (by rw [rt]; have := thread.isLt; omega)
    (by rw [rb,rt]; have := thread.isLt; change base+thread.val*8+0<2^64; omega)
  unfold SharedStore.Valid
  rw [address,start]
  rw [rb,rt]
  change Valid64 base s.sharedBytes (base+thread.val*8)
  refine ⟨by omega,?_,by have := thread.isLt; omega,noWrap⟩
  simp [Nat.add_mod,aligned]

theorem update_valid (frame : Frame base thread s) (aligned : base%8=0)
    (k : Fin 8) (live : thread.val<active (current k)) :
    PTX.Reduction.Update.Valid s (readOffset k true) := by
  obtain ⟨rb,rt,start,room,noWrap⟩ := frame
  apply PTX.Reduction.Update.valid_of_active s (active (current k))
  · simpa only [rt] using live
  · exact (ranges k).2.2
  · omega
  · simpa only [start] using aligned
  · exact room
  · simpa only [start] using noWrap

theorem initial_pc : (SharedStore.finish s 0 8).pc=s.pc+3 := by
  simp [SharedStore.finish,put,assign,advance,Nat.add_assoc]

theorem update_pc : (finish s left right).pc=s.pc+6 := by
  simp [finish,loaded,prepared,put,assign,advance,Nat.add_assoc]

theorem initial_fetch : ∀ j : Fin 3,
    program[j.val]?=((SharedStore.code 0 8)[j.val]?).map Instr.data := by decide +kernel

theorem update_fetch : ∀ (k : Fin 8) (j : Fin 6),
    program[5+8*k.val+j.val]?=((PTX.Reduction.Update.code (readOffset k true))[j.val]?).map Instr.data := by
  decide +kernel

theorem guard_fetch : ∀ k : Fin 8,
    program[4+8*k.val]?=some (.skip (active (current k)) (site (current k)+1)) := by decide +kernel

/-- A run between adjacent barrier positions contains no data instruction. -/
theorem barrier_events {start : State n} (run : Runs cfg code start events final)
    (forward : Forward code) (pcs : ∀ t, (start.lanes t).pc=boundary)
    (done : ∀ t, (final.lanes t).pc=boundary+1)
    (fetch : code[boundary]?=some (.sync 0)) :
    ∀ e, e∈events → ∃ b, e=Event.barrier b := by
  intro e member
  cases e with
  | barrier b => exact ⟨b,rfl⟩
  | data t a =>
    obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
    obtain ⟨eq,op,next,atPC,hd⟩ := step_access_origin hs hm
    subst selected
    have low := runs_pc_mono hp forward t
    have pc := access_pc hd
    have high := runs_pc_mono ht forward t
    rw [done,step_access_post hs hm] at high
    rw [pcs] at low
    have atBoundary : (before.lanes t).pc=boundary := by omega
    rw [atBoundary,fetch] at atPC
    cases atPC

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

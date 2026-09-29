import PoissonPTX.ConcurrentOwnership
import PoissonPTX.ContractionFetched

/-! Replay a store-free interval of actual concurrent execution. The snapshot
obligation concerns recorded loads, not a presumed arithmetic answer. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Replay

def view (memory : Space → Memory) (s : PTX.State) : PTX.State :=
  {s with global := memory .global, shared := memory .shared}

def noStore : Op → Bool
  | .store64 .. => false
  | _ => true

@[simp] theorem operand_view (memory : Space → Memory) (s : PTX.State) (o : Operand) :
    o.eval (view memory s)=o.eval s := by cases o <;> rfl

@[simp] theorem view_assign (memory : Space → Memory) (s : PTX.State) (r : Nat) (w : Word) :
    view memory (assign s r w)=assign (view memory s) r w := rfl

@[simp] theorem view_memory (memory : Space → Memory) (s : PTX.State) (sp : Space) :
    (view memory s).memory sp=memory sp := by cases sp <;> rfl

@[simp] theorem view_start (memory : Space → Memory) (s : PTX.State) (sp : Space) :
    (view memory s).start sp=s.start sp := by cases sp <;> rfl

@[simp] theorem view_bytes (memory : Space → Memory) (s : PTX.State) (sp : Space) :
    (view memory s).bytes sp=s.bytes sp := by cases sp <;> rfl

theorem ordinary_view (execution : Eval op s t) (plain : ordinary op=true) :
    Eval op (view memory s) (view memory t) := by
  cases execution <;> simp_all [ordinary]
  all_goals first
    | simpa using (Eval.mov (s:=view memory _))
    | simpa using (Eval.mul32 (s:=view memory _))
    | simpa using (Eval.add32 (s:=view memory _))
    | simpa using (Eval.add64 (s:=view memory _))
    | simpa using (Eval.wide8 (s:=view memory _))
    | exact Eval.fp (by simpa [FP.Result] using ‹FP.Result _ _ _ _›)

/-- Actual read bits agree with the snapshot, including NaN payloads. -/
theorem data_view (execution : Data op s t access) (nostore : noStore op=true)
    (reads : ∀ a, access=some a → a.data.store=false →
      a.data.value=read64 (memory a.space) a.data.address) :
    Eval op (view memory s) (view memory t) := by
  cases execution with
  | ordinary plain he => exact ordinary_view he plain
  | @load sp dst addr s word valid =>
    have hw := reads _ rfl rfl
    simp only at hw
    rw [view_assign,hw]
    simpa using (Eval.load64 (s:=view memory s) (dst:=dst) (address:=addr) (space:=sp) (by simpa using valid))
  | store => simp [noStore] at nostore

/-- The same operations occupy this half-open interval in both programs. -/
def Slice (program : List Instr) (scalar : List Op) (lo hi : Nat) : Prop :=
  ∀ pc, lo≤pc → pc<hi → ∃ op,
    program[pc]?=some (.data op) ∧ scalar[pc]?=some op ∧ noStore op=true

def Reads (memory : Space → Memory) (thread : Fin n) (lo hi : Nat) (events : List (Event n)) : Prop :=
  ∀ a, Event.data thread a∈events → a.data.store=false → lo≤a.data.pc → a.data.pc<hi →
    a.data.value=read64 (memory a.space) a.data.address

/-- Other threads may interleave. A barrier cannot advance a thread inside a
straight-line interval of data instructions. -/
theorem step_view (step : Step cfg program selected s out) (aligned : Aligned s)
    (slice : Slice program scalar lo hi) (before : lo≤(s.lanes thread).pc)
    (after : (out.state.lanes thread).pc≤hi) (forward : Forward program)
    (reads : Reads memory thread lo hi out.events) :
    view memory (s.lanes thread)=view memory (out.state.lanes thread) ∨
    PTX.Step scalar (view memory (s.lanes thread)) (view memory (out.state.lanes thread)) := by
  have mono := step_pc_mono step forward thread
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | data hd =>
    by_cases eq : thread=selected
    · subst thread
      have pc := data_pc hd
      simp only [setLane,Function.update_self] at after ⊢
      have inside : (s.lanes selected).pc<hi := by omega
      obtain ⟨op,hp,hs,hn⟩ := slice _ before inside
      have same := Option.some.inj (fetch.symm.trans hp)
      cases same
      right; refine ⟨_,hs,data_view hd hn ?_⟩
      intro a ha read
      have apc := access_pc (ha ▸ hd)
      apply reads a _ read (by omega) (by omega)
      simp [ha]
    · left; simp [setLane,Function.update,eq]
  | @skip active target =>
    by_cases eq : thread=selected
    · subst thread
      have increase : (s.lanes selected).pc <
          (if selected.val<active then (s.lanes selected).pc+1 else target) := by
        split
        · omega
        · exact forward _ _ _ fetch
      simp only [setLane,Function.update_self] at after
      obtain ⟨op,hp,_,_⟩ := slice _ before (by omega)
      rw [hp] at fetch; simp at fetch
    · left; simp [setLane,Function.update,eq]
  | @sync resource =>
    simp only [synchronize] at after ⊢
    generalize hr : Ptx.Barrier.step (barrierConfig cfg s selected) s.barrier
      (barrierRequest cfg s selected resource)=result at after ⊢
    cases disposition : result.disposition with
    | rejectedWrongKey => simp
    | waiting => simp
    | released =>
      have rel : (Ptx.Barrier.step (barrierConfig cfg s selected) s.barrier
          (barrierRequest cfg s selected resource)).disposition=.released := by rw [hr,disposition]
      have pcs := release_aligned cfg s selected resource aligned rel thread
      simp only [disposition,advance] at after
      obtain ⟨op,hp,_,_⟩ := slice _ before (by omega)
      rw [← pcs,hp] at fetch; simp at fetch

/-- Project actual interval endpoints in an arbitrary interleaving. -/
theorem run_view (run : Runs cfg program start events final) (aligned : Aligned start)
    (slice : Slice program scalar lo hi) (forward : Forward program)
    (before : lo≤(start.lanes thread).pc) (after : (final.lanes thread).pc≤hi)
    (reads : Reads memory thread lo hi events) :
    PTX.Runs scalar (view memory (start.lanes thread)) (view memory (final.lanes thread)) := by
  induction run with
  | nil => exact .nil
  | cons step tail ih =>
    have nextBound := runs_pc_mono tail forward thread
    have mono := step_pc_mono step forward thread
    have one := step_view step aligned slice before (by omega) forward
      (fun a ha => reads a (List.mem_append_left _ ha))
    have rest := ih (step_aligned step aligned) (by omega) after
      (fun a ha => reads a (List.mem_append_right _ ha))
    rcases one with same | one
    · rw [same]; exact rest
    · exact .cons one rest

/-- Byte-source obligations supply Reads. The ordered numerical answer follows
from actual instructions, with no supplied arithmetic or scalar execution trace. -/
theorem contraction (run : Runs cfg program start events final) (aligned : Aligned start)
    (forward : Forward program) (pre suffix : List Op)
    (slice : Slice program (pre++Contraction.program width acc a b++suffix)
      pre.length (pre.length+(Contraction.program width acc a b).length))
    (pc : (start.lanes thread).pc=pre.length)
    (done : (final.lanes thread).pc=pre.length+(Contraction.program width acc a b).length)
    (reads : Reads memory thread pre.length (pre.length+(Contraction.program width acc a b).length) events)
    (allowed : Contraction.Accumulator acc)
    (valid : ∀ k<width, Contraction.Valid (view memory (start.lanes thread)) width k a ∧
      Contraction.Valid (view memory (start.lanes thread)) width k b) :
    decode ((final.lanes thread).regs acc)=
      Spec.get2 (Spec.matMulSpec (Contraction.leftTensor (view memory (start.lanes thread)) width a)
        (Contraction.rightTensor (view memory (start.lanes thread)) width b)) 0 0 := by
  have projected := run_view run aligned slice forward (by omega) (by omega) reads
  exact (Contraction.fetched_correct allowed valid pre suffix pc projected done).1

end PtxTorchLean.Poisson.PTX.Concurrent.Replay

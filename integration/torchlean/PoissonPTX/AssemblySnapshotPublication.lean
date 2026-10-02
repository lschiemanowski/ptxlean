import PoissonPTX.AssemblyArenaValues
import PoissonPTX.AssemblyRows

namespace PtxTorchLean.Poisson.PTX.Assembly.Snapshot

/-- Completed fetched executions against one initial snapshot. A separate
source-admission argument must justify this view for concurrent executions. -/
structure Finished (a : Arena n) (memory : Memory) (mask : Bool) where
  regs : Fin n → Registers
  final : Fin n → Flow.State
  run : ∀ i, Flow.Runs (a.context i)
    (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
    (a.start memory (regs i)) (final i)
  done : ∀ i, (final i).halted=true

variable {n : Nat} {a : Arena n} {memory : Memory} {mask : Bool} {i : Fin n}

def address (a : Arena n) (i : Fin n) : Nat := a.base.toNat+a.output.toNat+i.val*8

def word (c : Finished a memory mask) (i : Fin n) : Word :=
  read64 (c.final i).core.global (address a i)

theorem written (c : Finished a memory mask) (contents : a.Contents memory) (i : Fin n) :
    (c.final i).core.global=write64 memory (address a i) (word c i) ∧
      decode (word c i)=a.value memory i mask := by
  obtain ⟨stored,effect,value⟩ := a.complete memory (c.regs i) i contents mask (c.run i) (c.done i)
  have same : word c i=stored := by simp [word,address,effect]
  rw [a.value_eq memory (c.regs i) i contents mask] at value
  exact ⟨by rw [same]; exact effect,by rw [same]; exact value⟩

/-- Mathematical publication of the one actual output word per completed
thread. This does not assert CUDA visibility or concurrent source validity. -/
def publish (c : Finished a memory mask) : List (Fin n) → Memory
  | [] => memory
  | i::rest => write64 (publish c rest) (address a i) (word c i)

theorem published_word (c : Finished a memory mask) (order : List (Fin n)) (included : i∈order) :
    read64 (publish c order) (address a i)=word c i := by
  induction order with
  | nil => simp at included
  | cons j rest ih =>
    by_cases same : j=i
    · subst j; simp [publish]
    · have keep := read64_write64_disjoint (publish c rest) (address a j) (address a i) (word c j) (a.owners j i same)
      exact keep.trans (ih ((List.mem_cons.mp included).resolve_left (Ne.symm same)))

theorem published_value (c : Finished a memory mask) (contents : a.Contents memory)
    (order : List (Fin n)) (complete : ∀ i, i∈order) (i : Fin n) :
    decode (read64 (publish c order) (address a i))=a.value memory i mask := by
  rw [published_word c order (complete i)]
  exact (written c contents i).2

theorem published_outside (c : Finished a memory mask) (order : List (Fin n)) (p : Nat)
    (outside : ∀ i, p<address a i ∨ address a i+8≤p) : publish c order p=memory p := by
  induction order with
  | nil => rfl
  | cons i rest ih => rw [publish,write64_outside _ _ _ _ (outside i),ih]

/-- Existence is obtained from returning instruction executions, independently
of the universal publication result. -/
noncomputable def witness (a : Arena n) (memory : Memory) (contents : a.Contents memory)
    (regs : Fin n → Registers) (mask : Bool) : Finished a memory mask where
  regs := regs
  final := fun i => Classical.choose (a.exists memory (regs i) i contents mask)
  run := fun i => (Classical.choose_spec (a.exists memory (regs i) i contents mask)).1
  done := fun i => (Classical.choose_spec (a.exists memory (regs i) i contents mask)).2

/-- The representation premise specifies the ordered input index list. It
contains no output sum. Cell-value correspondence can instantiate values from
a previously proved publication of the element kernel. -/
theorem scatter (c : Finished a memory mask) (contents : a.Contents memory)
    (locations : List (Nat × Nat))
    (represented : ∀ i, a.row memory i=Rows.selected locations i.val)
    (order : List (Fin n)) (complete : ∀ i, i∈order) (i : Fin n) :
    decode (read64 (publish c order) (address a i))=
      if mask=true ∧ read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)≠0 then 0 else
        (Rows.contributions locations (a.elementValue memory)).foldl Correspondence.scatterStep (fun _ => 0) i.val := by
  rw [published_value c contents order complete i]
  unfold Arena.value
  rw [represented i,Rows.ordered]

end PtxTorchLean.Poisson.PTX.Assembly.Snapshot

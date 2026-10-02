import PoissonPTX.IndexSources
import PoissonPTX.IndexedMemory

namespace PtxTorchLean.Poisson.PTX.Indexed.Candidate

/-- Candidate loads choose bits freely. Byte-source constraints, kept separate
from this instruction relation, determine which choices are permitted. -/
inductive Data : Instr → PTX.State → PTX.State → Option Concurrent.Access → Option IndexSources.Access → Prop
  | data (step : Concurrent.Data op s t access) : Data (.data op) s t access none
  | mad32 : Data (.mad32 dst a scale b) s (assign s dst (mad s a scale b)) none none
  | wide4 : Data (.wide4 dst src) s (assign s dst (wide s src)) none none
  | load32 (valid : Valid32 s.globalStart s.globalBytes (s.regs addr).toNat) :
      Data (.load32 dst addr) s (assign s dst (word.setWidth 64)) none
        (some ⟨s.pc,(s.regs addr).toNat,word⟩)

def noGlobalStore : Instr → Bool
  | .data (.store64 .global ..) => false
  | _ => true

def noSharedLoad : Instr → Bool
  | .data (.load64 .shared ..) => false
  | _ => true

theorem data_pc (step : Data i s t access index) : t.pc=s.pc+1 := by
  cases step with
  | data step => exact Concurrent.data_pc step
  | _ => rfl

theorem data_global (step : Data i s t access index) (safe : noGlobalStore i=true) :
    t.global=s.global := by
  cases step with
  | data hd =>
    cases hd with
    | ordinary plain he => cases he <;> simp_all [Concurrent.ordinary] <;> rfl
    | load => rfl
    | @store sp => cases sp <;> simp_all [noGlobalStore]; rfl
  | _ => rfl

theorem store_shared (step : Data i s t (some access) index)
    (safe : noGlobalStore i=true) (store : access.data.store=true) : access.space=.shared := by
  cases step with
  | data hd => cases hd with
    | load => simp at store
    | @store sp => cases sp <;> simp_all [noGlobalStore]

theorem load_global (step : Data i s t (some access) index)
    (safe : noSharedLoad i=true) (read : access.data.store=false) : access.space=.global := by
  cases step with
  | data hd => cases hd with
    | store => simp at read
    | @load sp => cases sp <;> simp_all [noSharedLoad]

/-- Replay uses actual load bits, not a tensor answer. Stores keep their full
byte effects; this does not overwrite a lane's memory with an invented view. -/
theorem replay (step : Data i s t access index)
    (words : ∀ a, access=some a → a.data.store=false →
      a.data.value=read64 (s.memory a.space) a.data.address)
    (indices : ∀ a, index=some a → a.value=read32 s.global a.address) : Eval i s t := by
  cases step with
  | data hd =>
    apply Eval.data
    cases hd with
    | ordinary _ he => exact he
    | @load sp dst addr s word valid =>
      have same := words _ rfl rfl
      simp only at same
      rw [same]
      exact PTX.Eval.load64 valid
    | store valid => exact PTX.Eval.store64 valid
  | mad32 => exact .mad32
  | wide4 => exact .wide4
  | @load32 s addr dst word valid =>
    have same := indices _ rfl
    simp only at same
    rw [same]
    exact .load32 valid

inductive Block : List Instr → PTX.State → List Concurrent.Access → List IndexSources.Access → PTX.State → Prop
  | nil : Block [] s [] [] s
  | cons : Data i s t access index → Block rest t words indices u →
      Block (i::rest) s (access.toList++words) (index.toList++indices) u

theorem block_global (run : Block code s words indices t)
    (safe : ∀ i∈code, noGlobalStore i=true) : t.global=s.global := by
  induction run with
  | nil => rfl
  | cons step _ ih =>
    exact (ih (fun i hi => safe i (by simp [hi]))).trans (data_global step (safe _ (by simp)))

theorem block_store_shared (run : Block code s words indices t)
    (safe : ∀ i∈code, noGlobalStore i=true)
    (member : access∈words) (store : access.data.store=true) : access.space=.shared := by
  induction run with
  | nil => simp at member
  | @cons i s mid a idx rest words indices t step run ih =>
    rcases List.mem_append.mp member with first | later
    · have same : a=some access := by simpa using first
      exact store_shared (same ▸ step) (safe _ (by simp)) store
    · exact ih (fun i hi => safe i (by simp [hi])) later

theorem block_replay (run : Block code s words indices t)
    (safe : ∀ i∈code, noGlobalStore i=true ∧ noSharedLoad i=true)
    (wordValues : ∀ a∈words, a.data.store=false → a.data.value=read64 s.global a.data.address)
    (indexValues : ∀ a∈indices, a.value=read32 s.global a.address) : Indexed.Block code s t := by
  induction run with
  | nil => exact .nil
  | @cons i s mid a idx rest words indices t step run ih =>
    have saf := safe i (by simp)
    have unchanged := data_global step saf.1
    apply Indexed.Block.cons (replay step ?_ ?_)
    · apply ih (fun i hi => safe i (by simp [hi]))
      · intro a ha read
        rw [unchanged]
        exact wordValues a (List.mem_append_right _ ha) read
      · intro a ha
        rw [unchanged]
        exact indexValues a (List.mem_append_right _ ha)
    · intro access observed read
      have global := load_global (observed ▸ step) saf.2 read
      rw [global]
      exact wordValues _ (by simp [observed]) read
    · intro access observed
      exact indexValues _ (by simp [observed])

end PtxTorchLean.Poisson.PTX.Indexed.Candidate

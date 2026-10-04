import PoissonPTX.ScalarExecution
import PoissonPTX.ScalarSources
import PoissonPTX.ObservedReadWitness

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

def records (word : Option Concurrent.Access) (index : Option IndexSources.Access) : List Sources.Access :=
  word.toList.map Sources.word++index.toList.map Sources.index

def extra : Instr → Bool | .base .. | .store32 .. => false | _ => true

/-- A single actual instruction history records both four-byte flags and
binary64 words. Candidate loads remain arbitrary until source admission. -/
inductive Eval (ctx : Kernel.Context) : Instr → Flow.State → Flow.State → List Sources.Access → Prop where
  | base (actual : Flow.Observed.Eval ctx i s t word index) : Eval ctx (.base i) s t (records word index)
  | store32 {address value : Operand} (valid : Valid32 s.core.globalStart s.core.globalBytes (address.eval s.core).toNat) :
      Eval ctx (.store32 address value) s (put32 s (address.eval s.core).toNat (Kernel.u32 (value.eval s.core)))
        [Sources.flag s.core.pc true (address.eval s.core).toNat (Kernel.u32 (value.eval s.core))]
  | extra (plain : extra i=true) (actual : Scalar.Eval ctx i s t) : Eval ctx i s t []

def Step (ctx : Kernel.Context) (program : List Instr) (s t : Flow.State) (events : List Sources.Access) : Prop :=
  s.halted=false ∧ ∃ i, program[s.core.pc]?=some i ∧ Eval ctx i s t events

inductive Runs (ctx : Kernel.Context) (program : List Instr) : Flow.State → List Sources.Access → Flow.State → Prop where
  | nil : Runs ctx program s [] s
  | cons : Step ctx program s middle first → Runs ctx program middle rest t → Runs ctx program s (first++rest) t

inductive Sequence (ctx : Kernel.Context) : List Instr → Flow.State → List Sources.Access → Flow.State → Prop where
  | nil : Sequence ctx [] s [] s
  | cons : s.halted=false → Eval ctx i s middle first → Sequence ctx code middle rest t →
      Sequence ctx (i::code) s (first++rest) t

/-- A local-memory equality used only as a replay lemma; the source bridge
must establish it rather than asking callers for a desired loaded value. -/
def ReadValues (memory : Space → Memory) (events : List Sources.Access) : Prop :=
  ∀ a∈events, a.store=false → ∀ k : Fin 8, k.val<a.width.bytes → a.byte k.val=memory a.space (a.address+k.val)

theorem replay (actual : Eval ctx i s t events) (reads : ReadValues s.core.memory events) : Scalar.Eval ctx i s t := by
  cases actual with
  | extra plain actual => exact actual
  | store32 valid => exact .store32 valid
  | base actual =>
    apply Scalar.Eval.base
    cases actual with
    | simple ordinary => exact .simple ordinary
    | data actual =>
      apply Flow.Eval.data
      apply Indexed.Candidate.replay actual
      · intro a found read
        apply Sources.word_value
        intro k
        exact reads (Sources.word a) (by simp [records,found]) read k k.isLt
      · intro a found
        apply Sources.flag_value
        intro k
        exact reads (Sources.index a) (by simp [records,found]) rfl ⟨k.val,by have := k.isLt; omega⟩ k.isLt

theorem eval_witness (actual : Scalar.Eval ctx i s t) :
    ∃ events, Eval ctx i s t events ∧ ReadValues s.core.memory events := by
  cases actual with
  | base actual =>
    cases actual with
    | simple ordinary => exact ⟨[],.base (.simple ordinary),by simp [ReadValues]⟩
    | data actual =>
      obtain ⟨word,index,recorded,words,indices⟩ := Flow.Observed.data_read_witness actual
      refine ⟨_,.base (.data recorded),?_⟩
      intro a member read k small
      simp only [records,List.mem_append,List.mem_map] at member
      rcases member with ⟨wa,member,rfl⟩ | ⟨ia,member,rfl⟩
      · have same : word=some wa := by simpa using member
        have value := words wa same read
        change PTX.byte wa.data.value k.val=_
        rw [value,PTX.Sources.byte_read64]
        rfl
      · have same : index=some ia := by simpa using member
        have value := indices ia same
        have bound : k.val<4 := small
        rw [Sources.index,Sources.flag_byte _ _ _ _ ⟨k.val,bound⟩,value,IndexSources.byte_read32]
        rfl
  | store32 valid => exact ⟨_,.store32 valid,by simp [ReadValues,Sources.flag]⟩
  | simple ordinary =>
    refine ⟨[],.extra ?_ (.simple ordinary),by simp [ReadValues]⟩
    cases i <;> simp_all [Scalar.ordinary,extra]
  | sqrt allowed => exact ⟨[],.extra rfl (.sqrt allowed),by simp [ReadValues]⟩
  | max allowed => exact ⟨[],.extra rfl (.max allowed),by simp [ReadValues]⟩
  | predFP enabled allowed => exact ⟨[],.extra rfl (.predFP enabled allowed),by simp [ReadValues]⟩
  | skipFP disabled => exact ⟨[],.extra rfl (.skipFP disabled),by simp [ReadValues]⟩

end PtxTorchLean.Poisson.PTX.Scalar.Observed

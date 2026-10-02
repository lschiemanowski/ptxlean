import PoissonPTX.ObservedPublication
import PoissonPTX.ObservedParallel
import PoissonPTX.CellWholeSources

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
variable {n : Nat} {ctx : Fin n → Kernel.Context} {s t : Fin n → State}
  {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}
  {memory : Memory} {p address : Nat} {thread : Fin n}

/-- At a byte untouched by other threads, merging the actual joint store
records agrees with the selected thread's actual final local byte. This needs
neither a supplied store occurrence nor a chosen output value. -/
theorem publication_byte (run : Runs ctx program s words indices t)
    (initial : memory p=(s thread).core.global p)
    (outside : ∀ owner access, Concurrent.Event.data owner access∈words → owner≠thread →
      access.space=.global → access.data.store=true → p<access.data.address ∨ access.data.address+8≤p) :
    Concurrent.GlobalPublication.publish memory words p=(t thread).core.global p := by
  induction run generalizing memory with
  | nil => exact initial
  | @cons selected s middle access index words indices t step rest ih =>
    rw [Concurrent.GlobalPublication.append,Observed.applyEvent_eq]
    apply ih
    · by_cases same : selected=thread
      · subst selected
        simp only [Function.update_self]
        rw [Observed.step_memory step]
        exact Observed.applyAccess_congr initial
      · rw [Function.update_of_ne (Ne.symm same)]
        rw [Observed.applyAccess_outside]
        · exact initial
        · intro record recorded global store
          exact outside selected record (by simp [recorded]) same global store
    · intro owner record member different
      exact outside owner record (List.mem_append_right _ member) different

/-- The word-level statement retains all eight byte equalities; it does not
assume atomic publication of an eight-byte read. -/
theorem publication_word (run : Runs ctx program s words indices t)
    (initial : memory=(s thread).core.global)
    (outside : ∀ owner access, Concurrent.Event.data owner access∈words → owner≠thread →
      access.space=.global → access.data.store=true →
      address+8≤access.data.address ∨ access.data.address+8≤address) :
    read64 (Concurrent.GlobalPublication.publish memory words) address=read64 (t thread).core.global address := by
  apply Sources.word_eq_of_bytes
  intro k
  simp only [Sources.byte_read64]
  apply publication_byte run (by rw [initial])
  intro owner access member different global store
  have apart := outside owner access member different global store
  have := k.isLt
  omega

end PtxTorchLean.Poisson.PTX.Flow.Parallel

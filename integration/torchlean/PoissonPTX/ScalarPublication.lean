import PoissonPTX.ScalarSources

namespace PtxTorchLean.Poisson.PTX.Scalar.Sources
variable {a : Access} {byte : Nat}

def applyAccess (memory : Space → Memory) (a : Access) : Space → Memory :=
  fun space => if a.store && decide (a.space=space) then
    match a.width with
    | .word => write64 (memory space) a.address a.value
    | .flag => write32 (memory space) a.address (a.value.setWidth 32)
  else memory space

def publish (memory : Space → Memory) : List Access → Space → Memory
  | [] => memory
  | a::rest => publish (applyAccess memory a) rest

theorem publish_append (memory : Space → Memory) (one two : List Access) :
    publish memory (one++two)=publish (publish memory one) two := by
  induction one generalizing memory with
  | nil => rfl
  | cons a rest ih => exact ih _

theorem apply_read (read : a.store=false) : applyAccess memory a=memory := by
  funext space
  unfold applyAccess
  rw [read]
  rfl

theorem apply_outside (apart : a.store=true → a.space=space → byte<a.address ∨ a.address+a.width.bytes≤byte) :
    applyAccess memory a space byte=memory space byte := by
  unfold applyAccess
  split
  · rename_i writes
    have info : a.store=true ∧ a.space=space := by simpa using writes
    have outside := apart info.1 info.2
    cases width:a.width with
    | word => exact write64_outside _ _ _ _ (by simpa [width,Width.bytes] using outside)
    | flag => exact write32_outside _ _ _ _ (by simpa [width,Width.bytes] using outside)
  · rfl

theorem publish_outside (apart : ∀ a∈events, a.store=true → a.space=space → byte<a.address ∨ a.address+a.width.bytes≤byte) :
    publish memory events space byte=memory space byte := by
  induction events generalizing memory with
  | nil => rfl
  | cons a rest ih =>
    exact (ih (fun a mem => apart a (by simp [mem]))).trans (apply_outside (apart a (by simp)))

end PtxTorchLean.Poisson.PTX.Scalar.Sources

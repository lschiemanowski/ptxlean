import PoissonPTX.ScalarStartResult

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena} {s : Flow.State}

def publish (a : Arena) (memory : Memory) (norm tolerance : Word) : Memory :=
  write32 (write32 (write64 (write64 (write64 memory (a.slot .rhsNorm) norm)
    (a.slot .residual) norm) (a.slot .tolerance) tolerance) (a.slot .active) 1) (a.slot .broken) 0

theorem result_publication (result : Result a s final) (ready : a.Ready s) :
    ∃ norm product tolerance,
      decode norm=Float.sqrt (decode (read64 s.core.global (a.slot .rhsSquare))) ∧
      decode product=decode (read64 s.core.global (a.slot .rtol))*decode norm ∧
      decode tolerance=maximum product (read64 s.core.global (a.slot .atol)) ∧
      final.core.global=publish a s.core.global norm tolerance := by
  obtain ⟨norm,product,tolerance,hn,hp,ht,rfl⟩ := result
  refine ⟨norm,product,tolerance,hn,hp,ht,?_⟩
  rw [tail_global (maximum_ready (scaled_ready (middle_ready (rooted_ready ready))))]
  simp only [maximumStored,scaled,assign,advance,Function.update_self]
  rw [(middle_values (rooted_ready ready)).2.2.2]
  simp only [rooted,Norm.rooted_frame.1,Norm.rooted_frame.2.2.2.2.2,publish]

theorem published_fields (a : Arena) (memory : Memory) (norm tolerance : Word) :
    read64 (publish a memory norm tolerance) (a.slot .rhsNorm)=norm ∧
    read64 (publish a memory norm tolerance) (a.slot .residual)=norm ∧
    read64 (publish a memory norm tolerance) (a.slot .tolerance)=tolerance ∧
    read32 (publish a memory norm tolerance) (a.slot .active)=1 ∧
    read32 (publish a memory norm tolerance) (a.slot .broken)=0 := by
  simp only [publish,
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .broken .rhsNorm (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .active .rhsNorm (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .broken .residual (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .active .residual (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .broken .tolerance (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .active .tolerance (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .tolerance .rhsNorm (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .residual .rhsNorm (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .tolerance .residual (by decide) rfl rfl),
    read32_write32_disjoint _ _ _ _ (a.separate .broken .active (by decide)),read64_write64,read32_write32,and_self]

theorem published_outside (a : Arena) (memory : Memory) (norm tolerance : Word) (byte : Nat)
    (outside : ∀ f∈[Field.rhsNorm,.residual,.tolerance,.active,.broken],byte<a.slot f ∨ a.slot f+f.width≤byte) :
    publish a memory norm tolerance byte=memory byte := by
  unfold publish
  rw [write32_outside _ _ _ _ (outside .broken (by simp)),write32_outside _ _ _ _ (outside .active (by simp)),
    write64_outside _ _ _ _ (outside .tolerance (by simp)),write64_outside _ _ _ _ (outside .residual (by simp)),
    write64_outside _ _ _ _ (outside .rhsNorm (by simp))]

theorem entry_publication
    (run : Runs a.context (entry a.offset) (a.start memory regs) final) (done : final.halted=true) :
    ∃ norm product tolerance,
      decode norm=Float.sqrt (decode (read64 memory (a.slot .rhsSquare))) ∧
      decode product=decode (read64 memory (a.slot .rtol))*decode norm ∧
      decode tolerance=maximum product (read64 memory (a.slot .atol)) ∧
      final.core.global=publish a memory norm tolerance := by
  obtain ⟨middle,trace,eq⟩ := entry_result run rfl rfl done body_segment
  obtain ⟨norm,product,tolerance,hn,hp,ht,global⟩ := result_publication
    (body_result trace rfl (a.setup_ready memory regs)) (a.setup_ready memory regs)
  subst final
  exact ⟨norm,product,tolerance,hn,hp,ht,global⟩

end PtxTorchLean.Poisson.PTX.Scalar.Start

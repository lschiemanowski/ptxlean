import PoissonPTX.DotStoreSyntax
import PoissonPTX.DotInputComplete
import PoissonPTX.ObservedReadWitness

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem input_global_frame
    (actual : Flow.Observed.Eval ctx i s t access index) (safe : inputSafe i=true) :
    t.core.global=s.core.global := by
  cases actual with
  | data step =>
    apply Indexed.Candidate.data_global step
    cases ‹Indexed.Instr› with
    | data op => cases op <;> simp_all [inputSafe,Indexed.Candidate.noGlobalStore]
    | _ => rfl
  | simple ordinary =>
    cases i <;> simp_all [Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals split <;> rfl

theorem input_access_read
    (actual : Flow.Observed.Eval ctx i s t (some access) index) (safe : inputSafe i=true) :
    access.data.store=false ∧ access.space=.global := by
  cases actual with
  | data step => cases step with
    | data step => cases step with
      | @load sp => cases sp <;> simp_all [inputSafe]
      | store => simp [inputSafe] at safe

/-- Record the scalar input witness with its actual initialized global bytes.
The input program cannot modify them, regardless of loop iteration count. -/
theorem input_recorded
    (run : Flow.Runs ctx (DotInput.inputProgram count left right scratch) s t) :
    ∃ words indices, Flow.Observed.Runs ctx (DotInput.inputProgram count left right scratch) s words indices t ∧
      t.core.global=s.core.global ∧
      ∀ access∈words, access.data.store=false ∧ access.space=.global ∧
        access.data.value=read64 s.core.global access.data.address := by
  induction run with
  | nil => exact ⟨[],[],.nil,rfl,by simp⟩
  | @cons s middle t step rest ih =>
    obtain ⟨access,index,observed,wordValues,indexValues⟩ := Flow.Observed.step_read_witness step
    obtain ⟨running,i,fetch,effect⟩ := observed
    have safe := input_safe (List.mem_of_getElem? fetch)
    have frame := input_global_frame effect safe
    obtain ⟨words,indices,tail,finalFrame,good⟩ := ih
    refine ⟨_,_,.cons ⟨running,i,fetch,effect⟩ tail,finalFrame.trans frame,?_⟩
    intro a member
    rcases List.mem_append.mp member with now | later
    · have equal : access=some a := by simpa using now
      have props := input_access_read (equal ▸ effect) safe
      have value := wordValues a equal props.1
      exact ⟨props.1,props.2,by simpa only [props.2,PTX.State.memory] using value⟩
    · obtain ⟨read,space,value⟩ := good a later
      exact ⟨read,space,frame ▸ value⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

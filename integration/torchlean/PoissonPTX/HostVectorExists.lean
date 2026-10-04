import PoissonPTX.HostLaunch
import PoissonPTX.InitializeRounded
import PoissonPTX.RestartVectorsRounded
import PoissonPTX.UpdateXRZRounded
import PoissonPTX.AffineUpdateRounded
import PoissonPTX.FreshResidualRounded
import PoissonPTX.AssemblyRoundedExists

namespace PtxTorchLean.Poisson.PTX.Host

/-- The two assembly entries read the same row metadata; only their output
and boundary-masking policy differ. -/
theorem Layout.assembly_contents (a : Layout n e w)
    (contents : (a.assembly false).Contents memory) : (a.assembly probe).Contents memory :=
  ⟨contents.ordered,contents.last,contents.indices⟩

/-- Construct a returning, admitted complete vector launch from the shared
physical layout and actual initial bytes. Assembly alone needs valid row-index
contents; no result or completed local run is a premise. -/
theorem vector_exists (a : Layout n e w) (kind : VectorEntry) (memory : Memory)
    (contents : (a.assembly false).Contents memory) :
    ∃ output, VectorLaunch a (a.vectorCode kind) memory output := by
  cases kind with
  | «initialize» =>
    obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,admitted,_⟩ :=
      Initialize.Arena.rounded_exists a.initialize memory (fun _ _ => 0)
    exact ⟨_,(fun _ _ => 0),words,indices,final,_,_,actual,done,compatible,indexCompatible,admitted,rfl⟩
  | restart =>
    obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,admitted,_⟩ :=
      RestartVectors.Arena.rounded_exists a.restart memory (fun _ _ => 0)
    exact ⟨_,(fun _ _ => 0),words,indices,final,_,_,actual,done,compatible,indexCompatible,admitted,rfl⟩
  | updateXRZ =>
    obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,admitted,_⟩ :=
      a.updateXRZ.rounded_exists memory (fun _ _ => 0)
    exact ⟨_,(fun _ _ => 0),words,indices,final,_,_,actual,done,compatible,indexCompatible,admitted,rfl⟩
  | updateP =>
    obtain ⟨words,indices,final,actual,done,compatible,admitted,empty,_⟩ :=
      a.updateP.rounded_exists memory (fun _ _ => 0)
    refine ⟨_,(fun _ _ => 0),words,indices,final,_,(fun _ _ => .initial),actual,done,compatible,?_,admitted,rfl⟩
    rw [empty]; intro r reader read located; simp at located
  | residual =>
    obtain ⟨words,indices,final,actual,done,compatible,admitted,empty,_⟩ :=
      FreshResidual.Arena.rounded_exists a.residual memory (fun _ _ => 0)
    refine ⟨_,(fun _ _ => 0),words,indices,final,_,(fun _ _ => .initial),actual,done,compatible,?_,admitted,rfl⟩
    rw [empty]; intro r reader read located; simp at located
  | assembly probe =>
    obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,_⟩ :=
      (a.assembly probe).rounded_exists memory (fun _ _ => 0)
        (a.assembly_contents contents) (a.assembly_separated probe) (!probe)
    exact ⟨_,(fun _ _ => 0),words,indices,final,_,_,actual,done,compatible,indexCompatible,
      Concurrent.Visibility.initial_thread_sources,rfl⟩

end PtxTorchLean.Poisson.PTX.Host

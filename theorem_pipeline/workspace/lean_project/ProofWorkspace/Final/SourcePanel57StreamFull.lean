import ProofWorkspace.Final.SourcePanel57BoundsFull
import ProofWorkspace.Final.SourcePanel57ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel57Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨57, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel57Candidate := by
  have hlast : (sourcePanel57Checkpoint 54).2 = sourcePanel57Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨57, by decide⟩ sourcePanel57Seed
    sourcePanel57Checkpoint sourcePanel57Seed_checked sourcePanel57Checkpoint_zero
    sourcePanel57Chunks_checked).trans hlast

theorem sourcePanel57_stream_passes :
    sourcePanelCheck ⟨57, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨57, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨57, by decide⟩)
    sourcePanel57Candidate_stream).trans sourcePanel57Candidate_passes

end ReciprocalXi

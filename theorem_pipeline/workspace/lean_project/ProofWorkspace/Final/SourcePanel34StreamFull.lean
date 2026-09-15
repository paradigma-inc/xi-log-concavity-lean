import ProofWorkspace.Final.SourcePanel34BoundsFull
import ProofWorkspace.Final.SourcePanel34ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel34Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨34, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel34Candidate := by
  have hlast : (sourcePanel34Checkpoint 54).2 = sourcePanel34Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨34, by decide⟩ sourcePanel34Seed
    sourcePanel34Checkpoint sourcePanel34Seed_checked sourcePanel34Checkpoint_zero
    sourcePanel34Chunks_checked).trans hlast

theorem sourcePanel34_stream_passes :
    sourcePanelCheck ⟨34, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨34, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨34, by decide⟩)
    sourcePanel34Candidate_stream).trans sourcePanel34Candidate_passes

end ReciprocalXi

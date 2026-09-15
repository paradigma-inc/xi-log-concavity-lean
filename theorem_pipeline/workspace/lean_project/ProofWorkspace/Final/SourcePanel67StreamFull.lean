import ProofWorkspace.Final.SourcePanel67BoundsFull
import ProofWorkspace.Final.SourcePanel67ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel67Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨67, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel67Candidate := by
  have hlast : (sourcePanel67Checkpoint 54).2 = sourcePanel67Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨67, by decide⟩ sourcePanel67Seed
    sourcePanel67Checkpoint sourcePanel67Seed_checked sourcePanel67Checkpoint_zero
    sourcePanel67Chunks_checked).trans hlast

theorem sourcePanel67_stream_passes :
    sourcePanelCheck ⟨67, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨67, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨67, by decide⟩)
    sourcePanel67Candidate_stream).trans sourcePanel67Candidate_passes

end ReciprocalXi

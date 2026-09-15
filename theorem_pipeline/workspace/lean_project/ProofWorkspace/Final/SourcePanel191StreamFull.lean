import ProofWorkspace.Final.SourcePanel191BoundsFull
import ProofWorkspace.Final.SourcePanel191ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel191Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨191, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel191Candidate := by
  have hlast : (sourcePanel191Checkpoint 54).2 = sourcePanel191Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨191, by decide⟩ sourcePanel191Seed
    sourcePanel191Checkpoint sourcePanel191Seed_checked sourcePanel191Checkpoint_zero
    sourcePanel191Chunks_checked).trans hlast

theorem sourcePanel191_stream_passes :
    sourcePanelCheck ⟨191, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨191, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨191, by decide⟩)
    sourcePanel191Candidate_stream).trans sourcePanel191Candidate_passes

end ReciprocalXi

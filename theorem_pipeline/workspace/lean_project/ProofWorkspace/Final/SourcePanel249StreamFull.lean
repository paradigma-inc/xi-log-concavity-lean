import ProofWorkspace.Final.SourcePanel249BoundsFull
import ProofWorkspace.Final.SourcePanel249ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel249Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨249, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel249Candidate := by
  have hlast : (sourcePanel249Checkpoint 54).2 = sourcePanel249Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨249, by decide⟩ sourcePanel249Seed
    sourcePanel249Checkpoint sourcePanel249Seed_checked sourcePanel249Checkpoint_zero
    sourcePanel249Chunks_checked).trans hlast

theorem sourcePanel249_stream_passes :
    sourcePanelCheck ⟨249, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨249, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨249, by decide⟩)
    sourcePanel249Candidate_stream).trans sourcePanel249Candidate_passes

end ReciprocalXi

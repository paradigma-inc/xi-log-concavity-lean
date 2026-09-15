import ProofWorkspace.Final.SourcePanel192BoundsFull
import ProofWorkspace.Final.SourcePanel192ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel192Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨192, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel192Candidate := by
  have hlast : (sourcePanel192Checkpoint 54).2 = sourcePanel192Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨192, by decide⟩ sourcePanel192Seed
    sourcePanel192Checkpoint sourcePanel192Seed_checked sourcePanel192Checkpoint_zero
    sourcePanel192Chunks_checked).trans hlast

theorem sourcePanel192_stream_passes :
    sourcePanelCheck ⟨192, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨192, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨192, by decide⟩)
    sourcePanel192Candidate_stream).trans sourcePanel192Candidate_passes

end ReciprocalXi

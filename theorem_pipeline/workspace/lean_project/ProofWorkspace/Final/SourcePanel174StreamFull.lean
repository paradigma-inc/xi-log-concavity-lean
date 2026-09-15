import ProofWorkspace.Final.SourcePanel174BoundsFull
import ProofWorkspace.Final.SourcePanel174ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel174Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨174, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel174Candidate := by
  have hlast : (sourcePanel174Checkpoint 54).2 = sourcePanel174Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨174, by decide⟩ sourcePanel174Seed
    sourcePanel174Checkpoint sourcePanel174Seed_checked sourcePanel174Checkpoint_zero
    sourcePanel174Chunks_checked).trans hlast

theorem sourcePanel174_stream_passes :
    sourcePanelCheck ⟨174, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨174, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨174, by decide⟩)
    sourcePanel174Candidate_stream).trans sourcePanel174Candidate_passes

end ReciprocalXi

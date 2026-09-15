import ProofWorkspace.Final.SourcePanel304BoundsFull
import ProofWorkspace.Final.SourcePanel304ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel304Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨304, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel304Candidate := by
  have hlast : (sourcePanel304Checkpoint 54).2 = sourcePanel304Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨304, by decide⟩ sourcePanel304Seed
    sourcePanel304Checkpoint sourcePanel304Seed_checked sourcePanel304Checkpoint_zero
    sourcePanel304Chunks_checked).trans hlast

theorem sourcePanel304_stream_passes :
    sourcePanelCheck ⟨304, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨304, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨304, by decide⟩)
    sourcePanel304Candidate_stream).trans sourcePanel304Candidate_passes

end ReciprocalXi

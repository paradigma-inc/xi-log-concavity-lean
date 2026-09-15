import ProofWorkspace.Final.SourcePanel36BoundsFull
import ProofWorkspace.Final.SourcePanel36ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel36Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨36, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel36Candidate := by
  have hlast : (sourcePanel36Checkpoint 54).2 = sourcePanel36Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨36, by decide⟩ sourcePanel36Seed
    sourcePanel36Checkpoint sourcePanel36Seed_checked sourcePanel36Checkpoint_zero
    sourcePanel36Chunks_checked).trans hlast

theorem sourcePanel36_stream_passes :
    sourcePanelCheck ⟨36, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨36, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨36, by decide⟩)
    sourcePanel36Candidate_stream).trans sourcePanel36Candidate_passes

end ReciprocalXi

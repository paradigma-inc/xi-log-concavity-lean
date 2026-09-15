import ProofWorkspace.Final.SourcePanel3BoundsFull
import ProofWorkspace.Final.SourcePanel3ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel3Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨3, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel3Candidate := by
  have hlast : (sourcePanel3Checkpoint 54).2 = sourcePanel3Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨3, by decide⟩ sourcePanel3Seed
    sourcePanel3Checkpoint sourcePanel3Seed_checked sourcePanel3Checkpoint_zero
    sourcePanel3Chunks_checked).trans hlast

theorem sourcePanel3_stream_passes :
    sourcePanelCheck ⟨3, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨3, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨3, by decide⟩)
    sourcePanel3Candidate_stream).trans sourcePanel3Candidate_passes

end ReciprocalXi

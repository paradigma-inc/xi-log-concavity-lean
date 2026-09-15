import ProofWorkspace.Final.SourcePanel2BoundsFull
import ProofWorkspace.Final.SourcePanel2ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel2Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨2, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel2Candidate := by
  have hlast : (sourcePanel2Checkpoint 54).2 = sourcePanel2Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨2, by decide⟩ sourcePanel2Seed
    sourcePanel2Checkpoint sourcePanel2Seed_checked sourcePanel2Checkpoint_zero
    sourcePanel2Chunks_checked).trans hlast

theorem sourcePanel2_stream_passes :
    sourcePanelCheck ⟨2, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨2, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨2, by decide⟩)
    sourcePanel2Candidate_stream).trans sourcePanel2Candidate_passes

end ReciprocalXi

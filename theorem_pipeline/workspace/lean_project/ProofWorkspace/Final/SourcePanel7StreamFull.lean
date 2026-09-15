import ProofWorkspace.Final.SourcePanel7BoundsFull
import ProofWorkspace.Final.SourcePanel7ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel7Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨7, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel7Candidate := by
  have hlast : (sourcePanel7Checkpoint 54).2 = sourcePanel7Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨7, by decide⟩ sourcePanel7Seed
    sourcePanel7Checkpoint sourcePanel7Seed_checked sourcePanel7Checkpoint_zero
    sourcePanel7Chunks_checked).trans hlast

theorem sourcePanel7_stream_passes :
    sourcePanelCheck ⟨7, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨7, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨7, by decide⟩)
    sourcePanel7Candidate_stream).trans sourcePanel7Candidate_passes

end ReciprocalXi

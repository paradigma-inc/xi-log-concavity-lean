import ProofWorkspace.Final.SourcePanel82BoundsFull
import ProofWorkspace.Final.SourcePanel82ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel82Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨82, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel82Candidate := by
  have hlast : (sourcePanel82Checkpoint 54).2 = sourcePanel82Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨82, by decide⟩ sourcePanel82Seed
    sourcePanel82Checkpoint sourcePanel82Seed_checked sourcePanel82Checkpoint_zero
    sourcePanel82Chunks_checked).trans hlast

theorem sourcePanel82_stream_passes :
    sourcePanelCheck ⟨82, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨82, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨82, by decide⟩)
    sourcePanel82Candidate_stream).trans sourcePanel82Candidate_passes

end ReciprocalXi

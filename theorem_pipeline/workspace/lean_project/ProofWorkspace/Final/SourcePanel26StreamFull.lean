import ProofWorkspace.Final.SourcePanel26BoundsFull
import ProofWorkspace.Final.SourcePanel26ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel26Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨26, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel26Candidate := by
  have hlast : (sourcePanel26Checkpoint 54).2 = sourcePanel26Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨26, by decide⟩ sourcePanel26Seed
    sourcePanel26Checkpoint sourcePanel26Seed_checked sourcePanel26Checkpoint_zero
    sourcePanel26Chunks_checked).trans hlast

theorem sourcePanel26_stream_passes :
    sourcePanelCheck ⟨26, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨26, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨26, by decide⟩)
    sourcePanel26Candidate_stream).trans sourcePanel26Candidate_passes

end ReciprocalXi

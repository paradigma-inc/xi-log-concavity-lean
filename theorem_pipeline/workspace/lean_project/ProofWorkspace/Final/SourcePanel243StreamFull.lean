import ProofWorkspace.Final.SourcePanel243BoundsFull
import ProofWorkspace.Final.SourcePanel243ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel243Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨243, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel243Candidate := by
  have hlast : (sourcePanel243Checkpoint 54).2 = sourcePanel243Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨243, by decide⟩ sourcePanel243Seed
    sourcePanel243Checkpoint sourcePanel243Seed_checked sourcePanel243Checkpoint_zero
    sourcePanel243Chunks_checked).trans hlast

theorem sourcePanel243_stream_passes :
    sourcePanelCheck ⟨243, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨243, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨243, by decide⟩)
    sourcePanel243Candidate_stream).trans sourcePanel243Candidate_passes

end ReciprocalXi

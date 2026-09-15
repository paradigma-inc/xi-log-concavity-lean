import ProofWorkspace.Final.SourcePanel22BoundsFull
import ProofWorkspace.Final.SourcePanel22ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel22Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨22, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel22Candidate := by
  have hlast : (sourcePanel22Checkpoint 54).2 = sourcePanel22Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨22, by decide⟩ sourcePanel22Seed
    sourcePanel22Checkpoint sourcePanel22Seed_checked sourcePanel22Checkpoint_zero
    sourcePanel22Chunks_checked).trans hlast

theorem sourcePanel22_stream_passes :
    sourcePanelCheck ⟨22, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨22, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨22, by decide⟩)
    sourcePanel22Candidate_stream).trans sourcePanel22Candidate_passes

end ReciprocalXi

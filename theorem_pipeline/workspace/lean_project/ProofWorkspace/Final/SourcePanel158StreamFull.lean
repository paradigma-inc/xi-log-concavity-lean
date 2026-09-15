import ProofWorkspace.Final.SourcePanel158BoundsFull
import ProofWorkspace.Final.SourcePanel158ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel158Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨158, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel158Candidate := by
  have hlast : (sourcePanel158Checkpoint 54).2 = sourcePanel158Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨158, by decide⟩ sourcePanel158Seed
    sourcePanel158Checkpoint sourcePanel158Seed_checked sourcePanel158Checkpoint_zero
    sourcePanel158Chunks_checked).trans hlast

theorem sourcePanel158_stream_passes :
    sourcePanelCheck ⟨158, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨158, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨158, by decide⟩)
    sourcePanel158Candidate_stream).trans sourcePanel158Candidate_passes

end ReciprocalXi

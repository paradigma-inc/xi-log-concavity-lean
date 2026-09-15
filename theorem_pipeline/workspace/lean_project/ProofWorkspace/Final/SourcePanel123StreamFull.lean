import ProofWorkspace.Final.SourcePanel123BoundsFull
import ProofWorkspace.Final.SourcePanel123ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel123Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨123, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel123Candidate := by
  have hlast : (sourcePanel123Checkpoint 54).2 = sourcePanel123Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨123, by decide⟩ sourcePanel123Seed
    sourcePanel123Checkpoint sourcePanel123Seed_checked sourcePanel123Checkpoint_zero
    sourcePanel123Chunks_checked).trans hlast

theorem sourcePanel123_stream_passes :
    sourcePanelCheck ⟨123, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨123, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨123, by decide⟩)
    sourcePanel123Candidate_stream).trans sourcePanel123Candidate_passes

end ReciprocalXi

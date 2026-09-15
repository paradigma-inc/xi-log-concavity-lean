import ProofWorkspace.Final.SourcePanel258BoundsFull
import ProofWorkspace.Final.SourcePanel258ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel258Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨258, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel258Candidate := by
  have hlast : (sourcePanel258Checkpoint 54).2 = sourcePanel258Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨258, by decide⟩ sourcePanel258Seed
    sourcePanel258Checkpoint sourcePanel258Seed_checked sourcePanel258Checkpoint_zero
    sourcePanel258Chunks_checked).trans hlast

theorem sourcePanel258_stream_passes :
    sourcePanelCheck ⟨258, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨258, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨258, by decide⟩)
    sourcePanel258Candidate_stream).trans sourcePanel258Candidate_passes

end ReciprocalXi

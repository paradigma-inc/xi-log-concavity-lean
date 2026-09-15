import ProofWorkspace.Final.SourcePanel106BoundsFull
import ProofWorkspace.Final.SourcePanel106ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel106Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨106, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel106Candidate := by
  have hlast : (sourcePanel106Checkpoint 54).2 = sourcePanel106Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨106, by decide⟩ sourcePanel106Seed
    sourcePanel106Checkpoint sourcePanel106Seed_checked sourcePanel106Checkpoint_zero
    sourcePanel106Chunks_checked).trans hlast

theorem sourcePanel106_stream_passes :
    sourcePanelCheck ⟨106, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨106, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨106, by decide⟩)
    sourcePanel106Candidate_stream).trans sourcePanel106Candidate_passes

end ReciprocalXi

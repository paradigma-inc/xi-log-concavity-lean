import ProofWorkspace.Final.SourcePanel6BoundsFull
import ProofWorkspace.Final.SourcePanel6ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel6Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨6, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel6Candidate := by
  have hlast : (sourcePanel6Checkpoint 54).2 = sourcePanel6Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨6, by decide⟩ sourcePanel6Seed
    sourcePanel6Checkpoint sourcePanel6Seed_checked sourcePanel6Checkpoint_zero
    sourcePanel6Chunks_checked).trans hlast

theorem sourcePanel6_stream_passes :
    sourcePanelCheck ⟨6, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨6, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨6, by decide⟩)
    sourcePanel6Candidate_stream).trans sourcePanel6Candidate_passes

end ReciprocalXi

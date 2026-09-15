import ProofWorkspace.Final.SourcePanel44BoundsFull
import ProofWorkspace.Final.SourcePanel44ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel44Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨44, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel44Candidate := by
  have hlast : (sourcePanel44Checkpoint 54).2 = sourcePanel44Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨44, by decide⟩ sourcePanel44Seed
    sourcePanel44Checkpoint sourcePanel44Seed_checked sourcePanel44Checkpoint_zero
    sourcePanel44Chunks_checked).trans hlast

theorem sourcePanel44_stream_passes :
    sourcePanelCheck ⟨44, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨44, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨44, by decide⟩)
    sourcePanel44Candidate_stream).trans sourcePanel44Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel287BoundsFull
import ProofWorkspace.Final.SourcePanel287ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel287Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨287, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel287Candidate := by
  have hlast : (sourcePanel287Checkpoint 54).2 = sourcePanel287Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨287, by decide⟩ sourcePanel287Seed
    sourcePanel287Checkpoint sourcePanel287Seed_checked sourcePanel287Checkpoint_zero
    sourcePanel287Chunks_checked).trans hlast

theorem sourcePanel287_stream_passes :
    sourcePanelCheck ⟨287, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨287, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨287, by decide⟩)
    sourcePanel287Candidate_stream).trans sourcePanel287Candidate_passes

end ReciprocalXi

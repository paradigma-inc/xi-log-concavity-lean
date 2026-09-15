import ProofWorkspace.Final.SourcePanel141BoundsFull
import ProofWorkspace.Final.SourcePanel141ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel141Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨141, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel141Candidate := by
  have hlast : (sourcePanel141Checkpoint 54).2 = sourcePanel141Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨141, by decide⟩ sourcePanel141Seed
    sourcePanel141Checkpoint sourcePanel141Seed_checked sourcePanel141Checkpoint_zero
    sourcePanel141Chunks_checked).trans hlast

theorem sourcePanel141_stream_passes :
    sourcePanelCheck ⟨141, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨141, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨141, by decide⟩)
    sourcePanel141Candidate_stream).trans sourcePanel141Candidate_passes

end ReciprocalXi

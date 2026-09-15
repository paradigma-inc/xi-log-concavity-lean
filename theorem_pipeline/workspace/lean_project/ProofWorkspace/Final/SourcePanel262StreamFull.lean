import ProofWorkspace.Final.SourcePanel262BoundsFull
import ProofWorkspace.Final.SourcePanel262ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel262Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨262, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel262Candidate := by
  have hlast : (sourcePanel262Checkpoint 54).2 = sourcePanel262Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨262, by decide⟩ sourcePanel262Seed
    sourcePanel262Checkpoint sourcePanel262Seed_checked sourcePanel262Checkpoint_zero
    sourcePanel262Chunks_checked).trans hlast

theorem sourcePanel262_stream_passes :
    sourcePanelCheck ⟨262, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨262, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨262, by decide⟩)
    sourcePanel262Candidate_stream).trans sourcePanel262Candidate_passes

end ReciprocalXi

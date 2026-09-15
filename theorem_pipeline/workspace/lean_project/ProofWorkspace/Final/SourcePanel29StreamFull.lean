import ProofWorkspace.Final.SourcePanel29BoundsFull
import ProofWorkspace.Final.SourcePanel29ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel29Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨29, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel29Candidate := by
  have hlast : (sourcePanel29Checkpoint 54).2 = sourcePanel29Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨29, by decide⟩ sourcePanel29Seed
    sourcePanel29Checkpoint sourcePanel29Seed_checked sourcePanel29Checkpoint_zero
    sourcePanel29Chunks_checked).trans hlast

theorem sourcePanel29_stream_passes :
    sourcePanelCheck ⟨29, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨29, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨29, by decide⟩)
    sourcePanel29Candidate_stream).trans sourcePanel29Candidate_passes

end ReciprocalXi

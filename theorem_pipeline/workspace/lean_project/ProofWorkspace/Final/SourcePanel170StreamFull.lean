import ProofWorkspace.Final.SourcePanel170BoundsFull
import ProofWorkspace.Final.SourcePanel170ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel170Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨170, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel170Candidate := by
  have hlast : (sourcePanel170Checkpoint 54).2 = sourcePanel170Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨170, by decide⟩ sourcePanel170Seed
    sourcePanel170Checkpoint sourcePanel170Seed_checked sourcePanel170Checkpoint_zero
    sourcePanel170Chunks_checked).trans hlast

theorem sourcePanel170_stream_passes :
    sourcePanelCheck ⟨170, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨170, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨170, by decide⟩)
    sourcePanel170Candidate_stream).trans sourcePanel170Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel31BoundsFull
import ProofWorkspace.Final.SourcePanel31ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel31Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨31, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel31Candidate := by
  have hlast : (sourcePanel31Checkpoint 54).2 = sourcePanel31Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨31, by decide⟩ sourcePanel31Seed
    sourcePanel31Checkpoint sourcePanel31Seed_checked sourcePanel31Checkpoint_zero
    sourcePanel31Chunks_checked).trans hlast

theorem sourcePanel31_stream_passes :
    sourcePanelCheck ⟨31, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨31, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨31, by decide⟩)
    sourcePanel31Candidate_stream).trans sourcePanel31Candidate_passes

end ReciprocalXi

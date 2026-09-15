import ProofWorkspace.Final.SourcePanel219BoundsFull
import ProofWorkspace.Final.SourcePanel219ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel219Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨219, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel219Candidate := by
  have hlast : (sourcePanel219Checkpoint 54).2 = sourcePanel219Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨219, by decide⟩ sourcePanel219Seed
    sourcePanel219Checkpoint sourcePanel219Seed_checked sourcePanel219Checkpoint_zero
    sourcePanel219Chunks_checked).trans hlast

theorem sourcePanel219_stream_passes :
    sourcePanelCheck ⟨219, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨219, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨219, by decide⟩)
    sourcePanel219Candidate_stream).trans sourcePanel219Candidate_passes

end ReciprocalXi

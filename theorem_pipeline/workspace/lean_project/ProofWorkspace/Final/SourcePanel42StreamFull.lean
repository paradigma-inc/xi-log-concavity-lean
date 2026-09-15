import ProofWorkspace.Final.SourcePanel42BoundsFull
import ProofWorkspace.Final.SourcePanel42ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel42Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨42, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel42Candidate := by
  have hlast : (sourcePanel42Checkpoint 54).2 = sourcePanel42Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨42, by decide⟩ sourcePanel42Seed
    sourcePanel42Checkpoint sourcePanel42Seed_checked sourcePanel42Checkpoint_zero
    sourcePanel42Chunks_checked).trans hlast

theorem sourcePanel42_stream_passes :
    sourcePanelCheck ⟨42, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨42, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨42, by decide⟩)
    sourcePanel42Candidate_stream).trans sourcePanel42Candidate_passes

end ReciprocalXi

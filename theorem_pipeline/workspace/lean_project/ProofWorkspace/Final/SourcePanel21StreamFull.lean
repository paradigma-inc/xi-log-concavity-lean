import ProofWorkspace.Final.SourcePanel21BoundsFull
import ProofWorkspace.Final.SourcePanel21ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel21Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨21, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel21Candidate := by
  have hlast : (sourcePanel21Checkpoint 54).2 = sourcePanel21Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨21, by decide⟩ sourcePanel21Seed
    sourcePanel21Checkpoint sourcePanel21Seed_checked sourcePanel21Checkpoint_zero
    sourcePanel21Chunks_checked).trans hlast

theorem sourcePanel21_stream_passes :
    sourcePanelCheck ⟨21, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨21, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨21, by decide⟩)
    sourcePanel21Candidate_stream).trans sourcePanel21Candidate_passes

end ReciprocalXi

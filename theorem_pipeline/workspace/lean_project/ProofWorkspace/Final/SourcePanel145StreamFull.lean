import ProofWorkspace.Final.SourcePanel145BoundsFull
import ProofWorkspace.Final.SourcePanel145ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel145Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨145, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel145Candidate := by
  have hlast : (sourcePanel145Checkpoint 54).2 = sourcePanel145Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨145, by decide⟩ sourcePanel145Seed
    sourcePanel145Checkpoint sourcePanel145Seed_checked sourcePanel145Checkpoint_zero
    sourcePanel145Chunks_checked).trans hlast

theorem sourcePanel145_stream_passes :
    sourcePanelCheck ⟨145, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨145, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨145, by decide⟩)
    sourcePanel145Candidate_stream).trans sourcePanel145Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel193BoundsFull
import ProofWorkspace.Final.SourcePanel193ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel193Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨193, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel193Candidate := by
  have hlast : (sourcePanel193Checkpoint 54).2 = sourcePanel193Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨193, by decide⟩ sourcePanel193Seed
    sourcePanel193Checkpoint sourcePanel193Seed_checked sourcePanel193Checkpoint_zero
    sourcePanel193Chunks_checked).trans hlast

theorem sourcePanel193_stream_passes :
    sourcePanelCheck ⟨193, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨193, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨193, by decide⟩)
    sourcePanel193Candidate_stream).trans sourcePanel193Candidate_passes

end ReciprocalXi

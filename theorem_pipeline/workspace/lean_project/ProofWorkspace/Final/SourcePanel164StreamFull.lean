import ProofWorkspace.Final.SourcePanel164BoundsFull
import ProofWorkspace.Final.SourcePanel164ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel164Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨164, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel164Candidate := by
  have hlast : (sourcePanel164Checkpoint 54).2 = sourcePanel164Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨164, by decide⟩ sourcePanel164Seed
    sourcePanel164Checkpoint sourcePanel164Seed_checked sourcePanel164Checkpoint_zero
    sourcePanel164Chunks_checked).trans hlast

theorem sourcePanel164_stream_passes :
    sourcePanelCheck ⟨164, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨164, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨164, by decide⟩)
    sourcePanel164Candidate_stream).trans sourcePanel164Candidate_passes

end ReciprocalXi

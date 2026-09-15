import ProofWorkspace.Final.SourcePanel32BoundsFull
import ProofWorkspace.Final.SourcePanel32ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel32Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨32, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel32Candidate := by
  have hlast : (sourcePanel32Checkpoint 54).2 = sourcePanel32Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨32, by decide⟩ sourcePanel32Seed
    sourcePanel32Checkpoint sourcePanel32Seed_checked sourcePanel32Checkpoint_zero
    sourcePanel32Chunks_checked).trans hlast

theorem sourcePanel32_stream_passes :
    sourcePanelCheck ⟨32, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨32, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨32, by decide⟩)
    sourcePanel32Candidate_stream).trans sourcePanel32Candidate_passes

end ReciprocalXi

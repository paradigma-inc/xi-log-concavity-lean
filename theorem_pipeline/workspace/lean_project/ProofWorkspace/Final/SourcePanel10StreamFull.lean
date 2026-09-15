import ProofWorkspace.Final.SourcePanel10BoundsFull
import ProofWorkspace.Final.SourcePanel10ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel10Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨10, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel10Candidate := by
  have hlast : (sourcePanel10Checkpoint 54).2 = sourcePanel10Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨10, by decide⟩ sourcePanel10Seed
    sourcePanel10Checkpoint sourcePanel10Seed_checked sourcePanel10Checkpoint_zero
    sourcePanel10Chunks_checked).trans hlast

theorem sourcePanel10_stream_passes :
    sourcePanelCheck ⟨10, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨10, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨10, by decide⟩)
    sourcePanel10Candidate_stream).trans sourcePanel10Candidate_passes

end ReciprocalXi

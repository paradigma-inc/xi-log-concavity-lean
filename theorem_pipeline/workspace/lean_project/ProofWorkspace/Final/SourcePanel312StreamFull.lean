import ProofWorkspace.Final.SourcePanel312BoundsFull
import ProofWorkspace.Final.SourcePanel312ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel312Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨312, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel312Candidate := by
  have hlast : (sourcePanel312Checkpoint 54).2 = sourcePanel312Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨312, by decide⟩ sourcePanel312Seed
    sourcePanel312Checkpoint sourcePanel312Seed_checked sourcePanel312Checkpoint_zero
    sourcePanel312Chunks_checked).trans hlast

theorem sourcePanel312_stream_passes :
    sourcePanelCheck ⟨312, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨312, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨312, by decide⟩)
    sourcePanel312Candidate_stream).trans sourcePanel312Candidate_passes

end ReciprocalXi

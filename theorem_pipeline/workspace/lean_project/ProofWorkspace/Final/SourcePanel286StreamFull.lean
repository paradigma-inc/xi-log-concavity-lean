import ProofWorkspace.Final.SourcePanel286BoundsFull
import ProofWorkspace.Final.SourcePanel286ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel286Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨286, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel286Candidate := by
  have hlast : (sourcePanel286Checkpoint 54).2 = sourcePanel286Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨286, by decide⟩ sourcePanel286Seed
    sourcePanel286Checkpoint sourcePanel286Seed_checked sourcePanel286Checkpoint_zero
    sourcePanel286Chunks_checked).trans hlast

theorem sourcePanel286_stream_passes :
    sourcePanelCheck ⟨286, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨286, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨286, by decide⟩)
    sourcePanel286Candidate_stream).trans sourcePanel286Candidate_passes

end ReciprocalXi

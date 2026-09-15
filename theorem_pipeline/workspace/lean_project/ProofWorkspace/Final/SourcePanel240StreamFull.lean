import ProofWorkspace.Final.SourcePanel240BoundsFull
import ProofWorkspace.Final.SourcePanel240ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel240Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨240, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel240Candidate := by
  have hlast : (sourcePanel240Checkpoint 54).2 = sourcePanel240Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨240, by decide⟩ sourcePanel240Seed
    sourcePanel240Checkpoint sourcePanel240Seed_checked sourcePanel240Checkpoint_zero
    sourcePanel240Chunks_checked).trans hlast

theorem sourcePanel240_stream_passes :
    sourcePanelCheck ⟨240, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨240, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨240, by decide⟩)
    sourcePanel240Candidate_stream).trans sourcePanel240Candidate_passes

end ReciprocalXi

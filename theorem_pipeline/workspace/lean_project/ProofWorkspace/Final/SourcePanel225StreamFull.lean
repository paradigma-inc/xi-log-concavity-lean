import ProofWorkspace.Final.SourcePanel225BoundsFull
import ProofWorkspace.Final.SourcePanel225ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel225Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨225, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel225Candidate := by
  have hlast : (sourcePanel225Checkpoint 54).2 = sourcePanel225Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨225, by decide⟩ sourcePanel225Seed
    sourcePanel225Checkpoint sourcePanel225Seed_checked sourcePanel225Checkpoint_zero
    sourcePanel225Chunks_checked).trans hlast

theorem sourcePanel225_stream_passes :
    sourcePanelCheck ⟨225, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨225, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨225, by decide⟩)
    sourcePanel225Candidate_stream).trans sourcePanel225Candidate_passes

end ReciprocalXi

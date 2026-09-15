import ProofWorkspace.Final.SourcePanel165BoundsFull
import ProofWorkspace.Final.SourcePanel165ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel165Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨165, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel165Candidate := by
  have hlast : (sourcePanel165Checkpoint 54).2 = sourcePanel165Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨165, by decide⟩ sourcePanel165Seed
    sourcePanel165Checkpoint sourcePanel165Seed_checked sourcePanel165Checkpoint_zero
    sourcePanel165Chunks_checked).trans hlast

theorem sourcePanel165_stream_passes :
    sourcePanelCheck ⟨165, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨165, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨165, by decide⟩)
    sourcePanel165Candidate_stream).trans sourcePanel165Candidate_passes

end ReciprocalXi

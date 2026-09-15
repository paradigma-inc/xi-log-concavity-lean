import ProofWorkspace.Final.SourcePanel195BoundsFull
import ProofWorkspace.Final.SourcePanel195ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel195Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨195, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel195Candidate := by
  have hlast : (sourcePanel195Checkpoint 54).2 = sourcePanel195Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨195, by decide⟩ sourcePanel195Seed
    sourcePanel195Checkpoint sourcePanel195Seed_checked sourcePanel195Checkpoint_zero
    sourcePanel195Chunks_checked).trans hlast

theorem sourcePanel195_stream_passes :
    sourcePanelCheck ⟨195, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨195, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨195, by decide⟩)
    sourcePanel195Candidate_stream).trans sourcePanel195Candidate_passes

end ReciprocalXi

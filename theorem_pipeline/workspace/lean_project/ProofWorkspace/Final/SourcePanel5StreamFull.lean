import ProofWorkspace.Final.SourcePanel5BoundsFull
import ProofWorkspace.Final.SourcePanel5ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel5Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨5, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel5Candidate := by
  have hlast : (sourcePanel5Checkpoint 54).2 = sourcePanel5Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨5, by decide⟩ sourcePanel5Seed
    sourcePanel5Checkpoint sourcePanel5Seed_checked sourcePanel5Checkpoint_zero
    sourcePanel5Chunks_checked).trans hlast

theorem sourcePanel5_stream_passes :
    sourcePanelCheck ⟨5, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨5, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨5, by decide⟩)
    sourcePanel5Candidate_stream).trans sourcePanel5Candidate_passes

end ReciprocalXi

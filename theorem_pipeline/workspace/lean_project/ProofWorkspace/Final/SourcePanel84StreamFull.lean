import ProofWorkspace.Final.SourcePanel84BoundsFull
import ProofWorkspace.Final.SourcePanel84ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel84Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨84, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel84Candidate := by
  have hlast : (sourcePanel84Checkpoint 54).2 = sourcePanel84Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨84, by decide⟩ sourcePanel84Seed
    sourcePanel84Checkpoint sourcePanel84Seed_checked sourcePanel84Checkpoint_zero
    sourcePanel84Chunks_checked).trans hlast

theorem sourcePanel84_stream_passes :
    sourcePanelCheck ⟨84, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨84, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨84, by decide⟩)
    sourcePanel84Candidate_stream).trans sourcePanel84Candidate_passes

end ReciprocalXi

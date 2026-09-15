import ProofWorkspace.Final.SourcePanel89BoundsFull
import ProofWorkspace.Final.SourcePanel89ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel89Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨89, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel89Candidate := by
  have hlast : (sourcePanel89Checkpoint 54).2 = sourcePanel89Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨89, by decide⟩ sourcePanel89Seed
    sourcePanel89Checkpoint sourcePanel89Seed_checked sourcePanel89Checkpoint_zero
    sourcePanel89Chunks_checked).trans hlast

theorem sourcePanel89_stream_passes :
    sourcePanelCheck ⟨89, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨89, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨89, by decide⟩)
    sourcePanel89Candidate_stream).trans sourcePanel89Candidate_passes

end ReciprocalXi

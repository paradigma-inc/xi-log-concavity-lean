import ProofWorkspace.Final.SourcePanel167BoundsFull
import ProofWorkspace.Final.SourcePanel167ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel167Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨167, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel167Candidate := by
  have hlast : (sourcePanel167Checkpoint 54).2 = sourcePanel167Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨167, by decide⟩ sourcePanel167Seed
    sourcePanel167Checkpoint sourcePanel167Seed_checked sourcePanel167Checkpoint_zero
    sourcePanel167Chunks_checked).trans hlast

theorem sourcePanel167_stream_passes :
    sourcePanelCheck ⟨167, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨167, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨167, by decide⟩)
    sourcePanel167Candidate_stream).trans sourcePanel167Candidate_passes

end ReciprocalXi

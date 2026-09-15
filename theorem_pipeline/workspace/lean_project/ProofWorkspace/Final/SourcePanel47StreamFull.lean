import ProofWorkspace.Final.SourcePanel47BoundsFull
import ProofWorkspace.Final.SourcePanel47ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel47Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨47, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel47Candidate := by
  have hlast : (sourcePanel47Checkpoint 54).2 = sourcePanel47Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨47, by decide⟩ sourcePanel47Seed
    sourcePanel47Checkpoint sourcePanel47Seed_checked sourcePanel47Checkpoint_zero
    sourcePanel47Chunks_checked).trans hlast

theorem sourcePanel47_stream_passes :
    sourcePanelCheck ⟨47, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨47, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨47, by decide⟩)
    sourcePanel47Candidate_stream).trans sourcePanel47Candidate_passes

end ReciprocalXi

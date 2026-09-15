import ProofWorkspace.Final.SourcePanel74BoundsFull
import ProofWorkspace.Final.SourcePanel74ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel74Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨74, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel74Candidate := by
  have hlast : (sourcePanel74Checkpoint 54).2 = sourcePanel74Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨74, by decide⟩ sourcePanel74Seed
    sourcePanel74Checkpoint sourcePanel74Seed_checked sourcePanel74Checkpoint_zero
    sourcePanel74Chunks_checked).trans hlast

theorem sourcePanel74_stream_passes :
    sourcePanelCheck ⟨74, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨74, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨74, by decide⟩)
    sourcePanel74Candidate_stream).trans sourcePanel74Candidate_passes

end ReciprocalXi

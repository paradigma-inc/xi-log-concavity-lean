import ProofWorkspace.Final.SourcePanel159BoundsFull
import ProofWorkspace.Final.SourcePanel159ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel159Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨159, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel159Candidate := by
  have hlast : (sourcePanel159Checkpoint 54).2 = sourcePanel159Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨159, by decide⟩ sourcePanel159Seed
    sourcePanel159Checkpoint sourcePanel159Seed_checked sourcePanel159Checkpoint_zero
    sourcePanel159Chunks_checked).trans hlast

theorem sourcePanel159_stream_passes :
    sourcePanelCheck ⟨159, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨159, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨159, by decide⟩)
    sourcePanel159Candidate_stream).trans sourcePanel159Candidate_passes

end ReciprocalXi

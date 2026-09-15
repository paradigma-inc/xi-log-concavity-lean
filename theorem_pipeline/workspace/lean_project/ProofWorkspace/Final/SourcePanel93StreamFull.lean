import ProofWorkspace.Final.SourcePanel93BoundsFull
import ProofWorkspace.Final.SourcePanel93ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel93Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨93, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel93Candidate := by
  have hlast : (sourcePanel93Checkpoint 54).2 = sourcePanel93Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨93, by decide⟩ sourcePanel93Seed
    sourcePanel93Checkpoint sourcePanel93Seed_checked sourcePanel93Checkpoint_zero
    sourcePanel93Chunks_checked).trans hlast

theorem sourcePanel93_stream_passes :
    sourcePanelCheck ⟨93, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨93, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨93, by decide⟩)
    sourcePanel93Candidate_stream).trans sourcePanel93Candidate_passes

end ReciprocalXi

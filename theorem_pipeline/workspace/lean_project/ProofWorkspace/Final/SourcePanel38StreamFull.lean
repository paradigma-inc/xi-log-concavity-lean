import ProofWorkspace.Final.SourcePanel38BoundsFull
import ProofWorkspace.Final.SourcePanel38ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel38Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨38, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel38Candidate := by
  have hlast : (sourcePanel38Checkpoint 54).2 = sourcePanel38Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨38, by decide⟩ sourcePanel38Seed
    sourcePanel38Checkpoint sourcePanel38Seed_checked sourcePanel38Checkpoint_zero
    sourcePanel38Chunks_checked).trans hlast

theorem sourcePanel38_stream_passes :
    sourcePanelCheck ⟨38, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨38, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨38, by decide⟩)
    sourcePanel38Candidate_stream).trans sourcePanel38Candidate_passes

end ReciprocalXi

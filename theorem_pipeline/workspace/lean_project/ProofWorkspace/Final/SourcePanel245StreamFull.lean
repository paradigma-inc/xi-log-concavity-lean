import ProofWorkspace.Final.SourcePanel245BoundsFull
import ProofWorkspace.Final.SourcePanel245ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel245Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨245, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel245Candidate := by
  have hlast : (sourcePanel245Checkpoint 54).2 = sourcePanel245Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨245, by decide⟩ sourcePanel245Seed
    sourcePanel245Checkpoint sourcePanel245Seed_checked sourcePanel245Checkpoint_zero
    sourcePanel245Chunks_checked).trans hlast

theorem sourcePanel245_stream_passes :
    sourcePanelCheck ⟨245, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨245, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨245, by decide⟩)
    sourcePanel245Candidate_stream).trans sourcePanel245Candidate_passes

end ReciprocalXi

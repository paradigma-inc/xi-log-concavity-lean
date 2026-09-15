import ProofWorkspace.Final.SourcePanel70BoundsFull
import ProofWorkspace.Final.SourcePanel70ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel70Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨70, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel70Candidate := by
  have hlast : (sourcePanel70Checkpoint 54).2 = sourcePanel70Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨70, by decide⟩ sourcePanel70Seed
    sourcePanel70Checkpoint sourcePanel70Seed_checked sourcePanel70Checkpoint_zero
    sourcePanel70Chunks_checked).trans hlast

theorem sourcePanel70_stream_passes :
    sourcePanelCheck ⟨70, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨70, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨70, by decide⟩)
    sourcePanel70Candidate_stream).trans sourcePanel70Candidate_passes

end ReciprocalXi

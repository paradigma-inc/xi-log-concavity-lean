import ProofWorkspace.Final.SourcePanel206BoundsFull
import ProofWorkspace.Final.SourcePanel206ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel206Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨206, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel206Candidate := by
  have hlast : (sourcePanel206Checkpoint 54).2 = sourcePanel206Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨206, by decide⟩ sourcePanel206Seed
    sourcePanel206Checkpoint sourcePanel206Seed_checked sourcePanel206Checkpoint_zero
    sourcePanel206Chunks_checked).trans hlast

theorem sourcePanel206_stream_passes :
    sourcePanelCheck ⟨206, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨206, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨206, by decide⟩)
    sourcePanel206Candidate_stream).trans sourcePanel206Candidate_passes

end ReciprocalXi

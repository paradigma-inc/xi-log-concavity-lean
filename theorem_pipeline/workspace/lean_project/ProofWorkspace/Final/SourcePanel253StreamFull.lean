import ProofWorkspace.Final.SourcePanel253BoundsFull
import ProofWorkspace.Final.SourcePanel253ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel253Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨253, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel253Candidate := by
  have hlast : (sourcePanel253Checkpoint 54).2 = sourcePanel253Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨253, by decide⟩ sourcePanel253Seed
    sourcePanel253Checkpoint sourcePanel253Seed_checked sourcePanel253Checkpoint_zero
    sourcePanel253Chunks_checked).trans hlast

theorem sourcePanel253_stream_passes :
    sourcePanelCheck ⟨253, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨253, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨253, by decide⟩)
    sourcePanel253Candidate_stream).trans sourcePanel253Candidate_passes

end ReciprocalXi

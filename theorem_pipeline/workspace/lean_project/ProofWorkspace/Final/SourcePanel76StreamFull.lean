import ProofWorkspace.Final.SourcePanel76BoundsFull
import ProofWorkspace.Final.SourcePanel76ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel76Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨76, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel76Candidate := by
  have hlast : (sourcePanel76Checkpoint 54).2 = sourcePanel76Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨76, by decide⟩ sourcePanel76Seed
    sourcePanel76Checkpoint sourcePanel76Seed_checked sourcePanel76Checkpoint_zero
    sourcePanel76Chunks_checked).trans hlast

theorem sourcePanel76_stream_passes :
    sourcePanelCheck ⟨76, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨76, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨76, by decide⟩)
    sourcePanel76Candidate_stream).trans sourcePanel76Candidate_passes

end ReciprocalXi

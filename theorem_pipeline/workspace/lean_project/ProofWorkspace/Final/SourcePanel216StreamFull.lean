import ProofWorkspace.Final.SourcePanel216BoundsFull
import ProofWorkspace.Final.SourcePanel216ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel216Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨216, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel216Candidate := by
  have hlast : (sourcePanel216Checkpoint 54).2 = sourcePanel216Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨216, by decide⟩ sourcePanel216Seed
    sourcePanel216Checkpoint sourcePanel216Seed_checked sourcePanel216Checkpoint_zero
    sourcePanel216Chunks_checked).trans hlast

theorem sourcePanel216_stream_passes :
    sourcePanelCheck ⟨216, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨216, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨216, by decide⟩)
    sourcePanel216Candidate_stream).trans sourcePanel216Candidate_passes

end ReciprocalXi

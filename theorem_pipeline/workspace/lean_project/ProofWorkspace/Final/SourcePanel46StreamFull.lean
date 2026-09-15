import ProofWorkspace.Final.SourcePanel46BoundsFull
import ProofWorkspace.Final.SourcePanel46ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel46Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨46, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel46Candidate := by
  have hlast : (sourcePanel46Checkpoint 54).2 = sourcePanel46Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨46, by decide⟩ sourcePanel46Seed
    sourcePanel46Checkpoint sourcePanel46Seed_checked sourcePanel46Checkpoint_zero
    sourcePanel46Chunks_checked).trans hlast

theorem sourcePanel46_stream_passes :
    sourcePanelCheck ⟨46, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨46, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨46, by decide⟩)
    sourcePanel46Candidate_stream).trans sourcePanel46Candidate_passes

end ReciprocalXi

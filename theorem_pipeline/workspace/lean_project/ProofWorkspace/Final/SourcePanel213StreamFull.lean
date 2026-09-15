import ProofWorkspace.Final.SourcePanel213BoundsFull
import ProofWorkspace.Final.SourcePanel213ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel213Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨213, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel213Candidate := by
  have hlast : (sourcePanel213Checkpoint 54).2 = sourcePanel213Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨213, by decide⟩ sourcePanel213Seed
    sourcePanel213Checkpoint sourcePanel213Seed_checked sourcePanel213Checkpoint_zero
    sourcePanel213Chunks_checked).trans hlast

theorem sourcePanel213_stream_passes :
    sourcePanelCheck ⟨213, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨213, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨213, by decide⟩)
    sourcePanel213Candidate_stream).trans sourcePanel213Candidate_passes

end ReciprocalXi

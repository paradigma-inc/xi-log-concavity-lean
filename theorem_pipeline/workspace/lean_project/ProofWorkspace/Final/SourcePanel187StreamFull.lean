import ProofWorkspace.Final.SourcePanel187BoundsFull
import ProofWorkspace.Final.SourcePanel187ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel187Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨187, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel187Candidate := by
  have hlast : (sourcePanel187Checkpoint 54).2 = sourcePanel187Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨187, by decide⟩ sourcePanel187Seed
    sourcePanel187Checkpoint sourcePanel187Seed_checked sourcePanel187Checkpoint_zero
    sourcePanel187Chunks_checked).trans hlast

theorem sourcePanel187_stream_passes :
    sourcePanelCheck ⟨187, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨187, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨187, by decide⟩)
    sourcePanel187Candidate_stream).trans sourcePanel187Candidate_passes

end ReciprocalXi

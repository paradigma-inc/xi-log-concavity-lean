import ProofWorkspace.Final.SourcePanel146BoundsFull
import ProofWorkspace.Final.SourcePanel146ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel146Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨146, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel146Candidate := by
  have hlast : (sourcePanel146Checkpoint 54).2 = sourcePanel146Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨146, by decide⟩ sourcePanel146Seed
    sourcePanel146Checkpoint sourcePanel146Seed_checked sourcePanel146Checkpoint_zero
    sourcePanel146Chunks_checked).trans hlast

theorem sourcePanel146_stream_passes :
    sourcePanelCheck ⟨146, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨146, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨146, by decide⟩)
    sourcePanel146Candidate_stream).trans sourcePanel146Candidate_passes

end ReciprocalXi

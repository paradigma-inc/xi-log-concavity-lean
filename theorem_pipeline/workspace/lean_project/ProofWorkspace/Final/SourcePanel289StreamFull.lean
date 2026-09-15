import ProofWorkspace.Final.SourcePanel289BoundsFull
import ProofWorkspace.Final.SourcePanel289ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel289Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨289, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel289Candidate := by
  have hlast : (sourcePanel289Checkpoint 54).2 = sourcePanel289Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨289, by decide⟩ sourcePanel289Seed
    sourcePanel289Checkpoint sourcePanel289Seed_checked sourcePanel289Checkpoint_zero
    sourcePanel289Chunks_checked).trans hlast

theorem sourcePanel289_stream_passes :
    sourcePanelCheck ⟨289, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨289, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨289, by decide⟩)
    sourcePanel289Candidate_stream).trans sourcePanel289Candidate_passes

end ReciprocalXi

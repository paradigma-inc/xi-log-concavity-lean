import ProofWorkspace.Final.SourcePanel0BoundsFull
import ProofWorkspace.Final.SourcePanel0ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel0Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨0, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel0Candidate := by
  have hlast : (sourcePanel0Checkpoint 54).2 = sourcePanel0Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨0, by decide⟩ sourcePanel0Seed
    sourcePanel0Checkpoint sourcePanel0Seed_checked sourcePanel0Checkpoint_zero
    sourcePanel0Chunks_checked).trans hlast

theorem sourcePanel0_stream_passes :
    sourcePanelCheck ⟨0, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨0, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨0, by decide⟩)
    sourcePanel0Candidate_stream).trans sourcePanel0Candidate_passes

end ReciprocalXi

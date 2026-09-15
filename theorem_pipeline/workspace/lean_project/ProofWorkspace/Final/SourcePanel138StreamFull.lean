import ProofWorkspace.Final.SourcePanel138BoundsFull
import ProofWorkspace.Final.SourcePanel138ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel138Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨138, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel138Candidate := by
  have hlast : (sourcePanel138Checkpoint 54).2 = sourcePanel138Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨138, by decide⟩ sourcePanel138Seed
    sourcePanel138Checkpoint sourcePanel138Seed_checked sourcePanel138Checkpoint_zero
    sourcePanel138Chunks_checked).trans hlast

theorem sourcePanel138_stream_passes :
    sourcePanelCheck ⟨138, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨138, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨138, by decide⟩)
    sourcePanel138Candidate_stream).trans sourcePanel138Candidate_passes

end ReciprocalXi

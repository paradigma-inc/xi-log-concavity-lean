import ProofWorkspace.Final.SourcePanel15BoundsFull
import ProofWorkspace.Final.SourcePanel15ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel15Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨15, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel15Candidate := by
  have hlast : (sourcePanel15Checkpoint 54).2 = sourcePanel15Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨15, by decide⟩ sourcePanel15Seed
    sourcePanel15Checkpoint sourcePanel15Seed_checked sourcePanel15Checkpoint_zero
    sourcePanel15Chunks_checked).trans hlast

theorem sourcePanel15_stream_passes :
    sourcePanelCheck ⟨15, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨15, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨15, by decide⟩)
    sourcePanel15Candidate_stream).trans sourcePanel15Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel183BoundsFull
import ProofWorkspace.Final.SourcePanel183ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel183Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨183, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel183Candidate := by
  have hlast : (sourcePanel183Checkpoint 54).2 = sourcePanel183Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨183, by decide⟩ sourcePanel183Seed
    sourcePanel183Checkpoint sourcePanel183Seed_checked sourcePanel183Checkpoint_zero
    sourcePanel183Chunks_checked).trans hlast

theorem sourcePanel183_stream_passes :
    sourcePanelCheck ⟨183, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨183, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨183, by decide⟩)
    sourcePanel183Candidate_stream).trans sourcePanel183Candidate_passes

end ReciprocalXi

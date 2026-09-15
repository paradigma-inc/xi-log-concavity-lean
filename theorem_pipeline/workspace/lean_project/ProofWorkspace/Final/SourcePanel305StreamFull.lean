import ProofWorkspace.Final.SourcePanel305BoundsFull
import ProofWorkspace.Final.SourcePanel305ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel305Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨305, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel305Candidate := by
  have hlast : (sourcePanel305Checkpoint 54).2 = sourcePanel305Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨305, by decide⟩ sourcePanel305Seed
    sourcePanel305Checkpoint sourcePanel305Seed_checked sourcePanel305Checkpoint_zero
    sourcePanel305Chunks_checked).trans hlast

theorem sourcePanel305_stream_passes :
    sourcePanelCheck ⟨305, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨305, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨305, by decide⟩)
    sourcePanel305Candidate_stream).trans sourcePanel305Candidate_passes

end ReciprocalXi

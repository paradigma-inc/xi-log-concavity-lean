import ProofWorkspace.Final.SourcePanel55BoundsFull
import ProofWorkspace.Final.SourcePanel55ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel55Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨55, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel55Candidate := by
  have hlast : (sourcePanel55Checkpoint 54).2 = sourcePanel55Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨55, by decide⟩ sourcePanel55Seed
    sourcePanel55Checkpoint sourcePanel55Seed_checked sourcePanel55Checkpoint_zero
    sourcePanel55Chunks_checked).trans hlast

theorem sourcePanel55_stream_passes :
    sourcePanelCheck ⟨55, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨55, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨55, by decide⟩)
    sourcePanel55Candidate_stream).trans sourcePanel55Candidate_passes

end ReciprocalXi

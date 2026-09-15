import ProofWorkspace.Final.SourcePanel11BoundsFull
import ProofWorkspace.Final.SourcePanel11ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel11Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨11, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel11Candidate := by
  have hlast : (sourcePanel11Checkpoint 54).2 = sourcePanel11Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨11, by decide⟩ sourcePanel11Seed
    sourcePanel11Checkpoint sourcePanel11Seed_checked sourcePanel11Checkpoint_zero
    sourcePanel11Chunks_checked).trans hlast

theorem sourcePanel11_stream_passes :
    sourcePanelCheck ⟨11, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨11, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨11, by decide⟩)
    sourcePanel11Candidate_stream).trans sourcePanel11Candidate_passes

end ReciprocalXi

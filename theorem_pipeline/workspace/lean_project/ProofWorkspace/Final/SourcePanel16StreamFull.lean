import ProofWorkspace.Final.SourcePanel16BoundsFull
import ProofWorkspace.Final.SourcePanel16ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel16Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨16, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel16Candidate := by
  have hlast : (sourcePanel16Checkpoint 54).2 = sourcePanel16Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨16, by decide⟩ sourcePanel16Seed
    sourcePanel16Checkpoint sourcePanel16Seed_checked sourcePanel16Checkpoint_zero
    sourcePanel16Chunks_checked).trans hlast

theorem sourcePanel16_stream_passes :
    sourcePanelCheck ⟨16, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨16, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨16, by decide⟩)
    sourcePanel16Candidate_stream).trans sourcePanel16Candidate_passes

end ReciprocalXi

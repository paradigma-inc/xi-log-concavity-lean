import ProofWorkspace.Final.SourcePanel125BoundsFull
import ProofWorkspace.Final.SourcePanel125ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel125Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨125, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel125Candidate := by
  have hlast : (sourcePanel125Checkpoint 54).2 = sourcePanel125Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨125, by decide⟩ sourcePanel125Seed
    sourcePanel125Checkpoint sourcePanel125Seed_checked sourcePanel125Checkpoint_zero
    sourcePanel125Chunks_checked).trans hlast

theorem sourcePanel125_stream_passes :
    sourcePanelCheck ⟨125, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨125, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨125, by decide⟩)
    sourcePanel125Candidate_stream).trans sourcePanel125Candidate_passes

end ReciprocalXi

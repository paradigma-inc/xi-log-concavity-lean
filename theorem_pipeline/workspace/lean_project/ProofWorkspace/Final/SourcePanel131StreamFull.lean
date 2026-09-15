import ProofWorkspace.Final.SourcePanel131BoundsFull
import ProofWorkspace.Final.SourcePanel131ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel131Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨131, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel131Candidate := by
  have hlast : (sourcePanel131Checkpoint 54).2 = sourcePanel131Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨131, by decide⟩ sourcePanel131Seed
    sourcePanel131Checkpoint sourcePanel131Seed_checked sourcePanel131Checkpoint_zero
    sourcePanel131Chunks_checked).trans hlast

theorem sourcePanel131_stream_passes :
    sourcePanelCheck ⟨131, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨131, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨131, by decide⟩)
    sourcePanel131Candidate_stream).trans sourcePanel131Candidate_passes

end ReciprocalXi

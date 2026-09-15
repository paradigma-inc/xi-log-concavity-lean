import ProofWorkspace.Final.SourcePanel308BoundsFull
import ProofWorkspace.Final.SourcePanel308ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel308Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨308, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel308Candidate := by
  have hlast : (sourcePanel308Checkpoint 54).2 = sourcePanel308Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨308, by decide⟩ sourcePanel308Seed
    sourcePanel308Checkpoint sourcePanel308Seed_checked sourcePanel308Checkpoint_zero
    sourcePanel308Chunks_checked).trans hlast

theorem sourcePanel308_stream_passes :
    sourcePanelCheck ⟨308, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨308, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨308, by decide⟩)
    sourcePanel308Candidate_stream).trans sourcePanel308Candidate_passes

end ReciprocalXi

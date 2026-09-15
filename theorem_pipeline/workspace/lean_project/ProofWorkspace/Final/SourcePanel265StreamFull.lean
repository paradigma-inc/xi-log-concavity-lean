import ProofWorkspace.Final.SourcePanel265BoundsFull
import ProofWorkspace.Final.SourcePanel265ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel265Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨265, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel265Candidate := by
  have hlast : (sourcePanel265Checkpoint 54).2 = sourcePanel265Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨265, by decide⟩ sourcePanel265Seed
    sourcePanel265Checkpoint sourcePanel265Seed_checked sourcePanel265Checkpoint_zero
    sourcePanel265Chunks_checked).trans hlast

theorem sourcePanel265_stream_passes :
    sourcePanelCheck ⟨265, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨265, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨265, by decide⟩)
    sourcePanel265Candidate_stream).trans sourcePanel265Candidate_passes

end ReciprocalXi

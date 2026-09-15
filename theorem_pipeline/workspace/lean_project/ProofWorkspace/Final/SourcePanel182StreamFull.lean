import ProofWorkspace.Final.SourcePanel182BoundsFull
import ProofWorkspace.Final.SourcePanel182ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel182Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨182, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel182Candidate := by
  have hlast : (sourcePanel182Checkpoint 54).2 = sourcePanel182Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨182, by decide⟩ sourcePanel182Seed
    sourcePanel182Checkpoint sourcePanel182Seed_checked sourcePanel182Checkpoint_zero
    sourcePanel182Chunks_checked).trans hlast

theorem sourcePanel182_stream_passes :
    sourcePanelCheck ⟨182, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨182, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨182, by decide⟩)
    sourcePanel182Candidate_stream).trans sourcePanel182Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel180BoundsFull
import ProofWorkspace.Final.SourcePanel180ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel180Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨180, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel180Candidate := by
  have hlast : (sourcePanel180Checkpoint 54).2 = sourcePanel180Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨180, by decide⟩ sourcePanel180Seed
    sourcePanel180Checkpoint sourcePanel180Seed_checked sourcePanel180Checkpoint_zero
    sourcePanel180Chunks_checked).trans hlast

theorem sourcePanel180_stream_passes :
    sourcePanelCheck ⟨180, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨180, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨180, by decide⟩)
    sourcePanel180Candidate_stream).trans sourcePanel180Candidate_passes

end ReciprocalXi

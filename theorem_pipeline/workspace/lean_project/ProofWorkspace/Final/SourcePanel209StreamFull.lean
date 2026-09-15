import ProofWorkspace.Final.SourcePanel209BoundsFull
import ProofWorkspace.Final.SourcePanel209ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel209Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨209, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel209Candidate := by
  have hlast : (sourcePanel209Checkpoint 54).2 = sourcePanel209Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨209, by decide⟩ sourcePanel209Seed
    sourcePanel209Checkpoint sourcePanel209Seed_checked sourcePanel209Checkpoint_zero
    sourcePanel209Chunks_checked).trans hlast

theorem sourcePanel209_stream_passes :
    sourcePanelCheck ⟨209, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨209, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨209, by decide⟩)
    sourcePanel209Candidate_stream).trans sourcePanel209Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel72BoundsFull
import ProofWorkspace.Final.SourcePanel72ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel72Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨72, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel72Candidate := by
  have hlast : (sourcePanel72Checkpoint 54).2 = sourcePanel72Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨72, by decide⟩ sourcePanel72Seed
    sourcePanel72Checkpoint sourcePanel72Seed_checked sourcePanel72Checkpoint_zero
    sourcePanel72Chunks_checked).trans hlast

theorem sourcePanel72_stream_passes :
    sourcePanelCheck ⟨72, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨72, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨72, by decide⟩)
    sourcePanel72Candidate_stream).trans sourcePanel72Candidate_passes

end ReciprocalXi

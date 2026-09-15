import ProofWorkspace.Final.SourcePanel50BoundsFull
import ProofWorkspace.Final.SourcePanel50ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel50Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨50, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel50Candidate := by
  have hlast : (sourcePanel50Checkpoint 54).2 = sourcePanel50Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨50, by decide⟩ sourcePanel50Seed
    sourcePanel50Checkpoint sourcePanel50Seed_checked sourcePanel50Checkpoint_zero
    sourcePanel50Chunks_checked).trans hlast

theorem sourcePanel50_stream_passes :
    sourcePanelCheck ⟨50, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨50, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨50, by decide⟩)
    sourcePanel50Candidate_stream).trans sourcePanel50Candidate_passes

end ReciprocalXi

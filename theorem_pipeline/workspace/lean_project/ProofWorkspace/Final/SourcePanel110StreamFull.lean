import ProofWorkspace.Final.SourcePanel110BoundsFull
import ProofWorkspace.Final.SourcePanel110ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel110Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨110, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel110Candidate := by
  have hlast : (sourcePanel110Checkpoint 54).2 = sourcePanel110Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨110, by decide⟩ sourcePanel110Seed
    sourcePanel110Checkpoint sourcePanel110Seed_checked sourcePanel110Checkpoint_zero
    sourcePanel110Chunks_checked).trans hlast

theorem sourcePanel110_stream_passes :
    sourcePanelCheck ⟨110, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨110, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨110, by decide⟩)
    sourcePanel110Candidate_stream).trans sourcePanel110Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel282BoundsFull
import ProofWorkspace.Final.SourcePanel282ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel282Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨282, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel282Candidate := by
  have hlast : (sourcePanel282Checkpoint 54).2 = sourcePanel282Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨282, by decide⟩ sourcePanel282Seed
    sourcePanel282Checkpoint sourcePanel282Seed_checked sourcePanel282Checkpoint_zero
    sourcePanel282Chunks_checked).trans hlast

theorem sourcePanel282_stream_passes :
    sourcePanelCheck ⟨282, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨282, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨282, by decide⟩)
    sourcePanel282Candidate_stream).trans sourcePanel282Candidate_passes

end ReciprocalXi

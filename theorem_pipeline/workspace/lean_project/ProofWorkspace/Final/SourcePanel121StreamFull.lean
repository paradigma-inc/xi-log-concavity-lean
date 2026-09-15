import ProofWorkspace.Final.SourcePanel121BoundsFull
import ProofWorkspace.Final.SourcePanel121ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel121Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨121, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel121Candidate := by
  have hlast : (sourcePanel121Checkpoint 54).2 = sourcePanel121Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨121, by decide⟩ sourcePanel121Seed
    sourcePanel121Checkpoint sourcePanel121Seed_checked sourcePanel121Checkpoint_zero
    sourcePanel121Chunks_checked).trans hlast

theorem sourcePanel121_stream_passes :
    sourcePanelCheck ⟨121, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨121, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨121, by decide⟩)
    sourcePanel121Candidate_stream).trans sourcePanel121Candidate_passes

end ReciprocalXi

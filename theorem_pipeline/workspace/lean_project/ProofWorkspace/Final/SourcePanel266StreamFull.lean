import ProofWorkspace.Final.SourcePanel266BoundsFull
import ProofWorkspace.Final.SourcePanel266ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel266Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨266, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel266Candidate := by
  have hlast : (sourcePanel266Checkpoint 54).2 = sourcePanel266Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨266, by decide⟩ sourcePanel266Seed
    sourcePanel266Checkpoint sourcePanel266Seed_checked sourcePanel266Checkpoint_zero
    sourcePanel266Chunks_checked).trans hlast

theorem sourcePanel266_stream_passes :
    sourcePanelCheck ⟨266, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨266, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨266, by decide⟩)
    sourcePanel266Candidate_stream).trans sourcePanel266Candidate_passes

end ReciprocalXi

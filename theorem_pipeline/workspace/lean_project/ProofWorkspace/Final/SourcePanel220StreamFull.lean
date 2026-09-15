import ProofWorkspace.Final.SourcePanel220BoundsFull
import ProofWorkspace.Final.SourcePanel220ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel220Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨220, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel220Candidate := by
  have hlast : (sourcePanel220Checkpoint 54).2 = sourcePanel220Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨220, by decide⟩ sourcePanel220Seed
    sourcePanel220Checkpoint sourcePanel220Seed_checked sourcePanel220Checkpoint_zero
    sourcePanel220Chunks_checked).trans hlast

theorem sourcePanel220_stream_passes :
    sourcePanelCheck ⟨220, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨220, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨220, by decide⟩)
    sourcePanel220Candidate_stream).trans sourcePanel220Candidate_passes

end ReciprocalXi

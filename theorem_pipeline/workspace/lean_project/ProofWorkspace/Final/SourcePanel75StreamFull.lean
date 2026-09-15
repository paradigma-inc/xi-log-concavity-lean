import ProofWorkspace.Final.SourcePanel75BoundsFull
import ProofWorkspace.Final.SourcePanel75ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel75Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨75, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel75Candidate := by
  have hlast : (sourcePanel75Checkpoint 54).2 = sourcePanel75Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨75, by decide⟩ sourcePanel75Seed
    sourcePanel75Checkpoint sourcePanel75Seed_checked sourcePanel75Checkpoint_zero
    sourcePanel75Chunks_checked).trans hlast

theorem sourcePanel75_stream_passes :
    sourcePanelCheck ⟨75, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨75, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨75, by decide⟩)
    sourcePanel75Candidate_stream).trans sourcePanel75Candidate_passes

end ReciprocalXi

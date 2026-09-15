import ProofWorkspace.Final.SourcePanel277BoundsFull
import ProofWorkspace.Final.SourcePanel277ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel277Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨277, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel277Candidate := by
  have hlast : (sourcePanel277Checkpoint 54).2 = sourcePanel277Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨277, by decide⟩ sourcePanel277Seed
    sourcePanel277Checkpoint sourcePanel277Seed_checked sourcePanel277Checkpoint_zero
    sourcePanel277Chunks_checked).trans hlast

theorem sourcePanel277_stream_passes :
    sourcePanelCheck ⟨277, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨277, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨277, by decide⟩)
    sourcePanel277Candidate_stream).trans sourcePanel277Candidate_passes

end ReciprocalXi

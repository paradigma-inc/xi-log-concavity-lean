import ProofWorkspace.Final.SourcePanel179BoundsFull
import ProofWorkspace.Final.SourcePanel179ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel179Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨179, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel179Candidate := by
  have hlast : (sourcePanel179Checkpoint 54).2 = sourcePanel179Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨179, by decide⟩ sourcePanel179Seed
    sourcePanel179Checkpoint sourcePanel179Seed_checked sourcePanel179Checkpoint_zero
    sourcePanel179Chunks_checked).trans hlast

theorem sourcePanel179_stream_passes :
    sourcePanelCheck ⟨179, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨179, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨179, by decide⟩)
    sourcePanel179Candidate_stream).trans sourcePanel179Candidate_passes

end ReciprocalXi

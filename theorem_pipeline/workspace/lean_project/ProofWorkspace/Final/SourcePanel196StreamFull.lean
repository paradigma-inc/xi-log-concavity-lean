import ProofWorkspace.Final.SourcePanel196BoundsFull
import ProofWorkspace.Final.SourcePanel196ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel196Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨196, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel196Candidate := by
  have hlast : (sourcePanel196Checkpoint 54).2 = sourcePanel196Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨196, by decide⟩ sourcePanel196Seed
    sourcePanel196Checkpoint sourcePanel196Seed_checked sourcePanel196Checkpoint_zero
    sourcePanel196Chunks_checked).trans hlast

theorem sourcePanel196_stream_passes :
    sourcePanelCheck ⟨196, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨196, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨196, by decide⟩)
    sourcePanel196Candidate_stream).trans sourcePanel196Candidate_passes

end ReciprocalXi

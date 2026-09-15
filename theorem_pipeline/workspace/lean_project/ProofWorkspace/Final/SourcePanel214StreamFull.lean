import ProofWorkspace.Final.SourcePanel214BoundsFull
import ProofWorkspace.Final.SourcePanel214ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel214Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨214, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel214Candidate := by
  have hlast : (sourcePanel214Checkpoint 54).2 = sourcePanel214Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨214, by decide⟩ sourcePanel214Seed
    sourcePanel214Checkpoint sourcePanel214Seed_checked sourcePanel214Checkpoint_zero
    sourcePanel214Chunks_checked).trans hlast

theorem sourcePanel214_stream_passes :
    sourcePanelCheck ⟨214, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨214, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨214, by decide⟩)
    sourcePanel214Candidate_stream).trans sourcePanel214Candidate_passes

end ReciprocalXi

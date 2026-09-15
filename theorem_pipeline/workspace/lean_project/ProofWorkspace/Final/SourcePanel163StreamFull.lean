import ProofWorkspace.Final.SourcePanel163BoundsFull
import ProofWorkspace.Final.SourcePanel163ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel163Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨163, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel163Candidate := by
  have hlast : (sourcePanel163Checkpoint 54).2 = sourcePanel163Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨163, by decide⟩ sourcePanel163Seed
    sourcePanel163Checkpoint sourcePanel163Seed_checked sourcePanel163Checkpoint_zero
    sourcePanel163Chunks_checked).trans hlast

theorem sourcePanel163_stream_passes :
    sourcePanelCheck ⟨163, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨163, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨163, by decide⟩)
    sourcePanel163Candidate_stream).trans sourcePanel163Candidate_passes

end ReciprocalXi

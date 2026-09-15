import ProofWorkspace.Final.SourcePanel300BoundsFull
import ProofWorkspace.Final.SourcePanel300ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel300Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨300, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel300Candidate := by
  have hlast : (sourcePanel300Checkpoint 54).2 = sourcePanel300Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨300, by decide⟩ sourcePanel300Seed
    sourcePanel300Checkpoint sourcePanel300Seed_checked sourcePanel300Checkpoint_zero
    sourcePanel300Chunks_checked).trans hlast

theorem sourcePanel300_stream_passes :
    sourcePanelCheck ⟨300, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨300, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨300, by decide⟩)
    sourcePanel300Candidate_stream).trans sourcePanel300Candidate_passes

end ReciprocalXi

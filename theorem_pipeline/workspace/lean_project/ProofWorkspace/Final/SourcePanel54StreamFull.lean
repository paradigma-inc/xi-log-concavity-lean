import ProofWorkspace.Final.SourcePanel54BoundsFull
import ProofWorkspace.Final.SourcePanel54ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel54Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨54, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel54Candidate := by
  have hlast : (sourcePanel54Checkpoint 54).2 = sourcePanel54Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨54, by decide⟩ sourcePanel54Seed
    sourcePanel54Checkpoint sourcePanel54Seed_checked sourcePanel54Checkpoint_zero
    sourcePanel54Chunks_checked).trans hlast

theorem sourcePanel54_stream_passes :
    sourcePanelCheck ⟨54, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨54, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨54, by decide⟩)
    sourcePanel54Candidate_stream).trans sourcePanel54Candidate_passes

end ReciprocalXi

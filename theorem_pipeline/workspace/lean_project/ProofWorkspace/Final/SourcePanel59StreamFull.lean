import ProofWorkspace.Final.SourcePanel59BoundsFull
import ProofWorkspace.Final.SourcePanel59ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel59Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨59, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel59Candidate := by
  have hlast : (sourcePanel59Checkpoint 54).2 = sourcePanel59Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨59, by decide⟩ sourcePanel59Seed
    sourcePanel59Checkpoint sourcePanel59Seed_checked sourcePanel59Checkpoint_zero
    sourcePanel59Chunks_checked).trans hlast

theorem sourcePanel59_stream_passes :
    sourcePanelCheck ⟨59, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨59, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨59, by decide⟩)
    sourcePanel59Candidate_stream).trans sourcePanel59Candidate_passes

end ReciprocalXi

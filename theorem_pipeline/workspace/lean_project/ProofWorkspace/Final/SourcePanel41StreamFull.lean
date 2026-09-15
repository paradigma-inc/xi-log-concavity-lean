import ProofWorkspace.Final.SourcePanel41BoundsFull
import ProofWorkspace.Final.SourcePanel41ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel41Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨41, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel41Candidate := by
  have hlast : (sourcePanel41Checkpoint 54).2 = sourcePanel41Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨41, by decide⟩ sourcePanel41Seed
    sourcePanel41Checkpoint sourcePanel41Seed_checked sourcePanel41Checkpoint_zero
    sourcePanel41Chunks_checked).trans hlast

theorem sourcePanel41_stream_passes :
    sourcePanelCheck ⟨41, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨41, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨41, by decide⟩)
    sourcePanel41Candidate_stream).trans sourcePanel41Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel172BoundsFull
import ProofWorkspace.Final.SourcePanel172ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel172Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨172, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel172Candidate := by
  have hlast : (sourcePanel172Checkpoint 54).2 = sourcePanel172Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨172, by decide⟩ sourcePanel172Seed
    sourcePanel172Checkpoint sourcePanel172Seed_checked sourcePanel172Checkpoint_zero
    sourcePanel172Chunks_checked).trans hlast

theorem sourcePanel172_stream_passes :
    sourcePanelCheck ⟨172, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨172, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨172, by decide⟩)
    sourcePanel172Candidate_stream).trans sourcePanel172Candidate_passes

end ReciprocalXi

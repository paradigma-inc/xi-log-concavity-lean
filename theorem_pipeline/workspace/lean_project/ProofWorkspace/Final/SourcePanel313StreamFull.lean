import ProofWorkspace.Final.SourcePanel313BoundsFull
import ProofWorkspace.Final.SourcePanel313ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel313Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨313, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel313Candidate := by
  have hlast : (sourcePanel313Checkpoint 54).2 = sourcePanel313Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨313, by decide⟩ sourcePanel313Seed
    sourcePanel313Checkpoint sourcePanel313Seed_checked sourcePanel313Checkpoint_zero
    sourcePanel313Chunks_checked).trans hlast

theorem sourcePanel313_stream_passes :
    sourcePanelCheck ⟨313, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨313, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨313, by decide⟩)
    sourcePanel313Candidate_stream).trans sourcePanel313Candidate_passes

end ReciprocalXi

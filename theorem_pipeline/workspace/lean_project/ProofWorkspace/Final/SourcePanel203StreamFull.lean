import ProofWorkspace.Final.SourcePanel203BoundsFull
import ProofWorkspace.Final.SourcePanel203ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel203Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨203, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel203Candidate := by
  have hlast : (sourcePanel203Checkpoint 54).2 = sourcePanel203Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨203, by decide⟩ sourcePanel203Seed
    sourcePanel203Checkpoint sourcePanel203Seed_checked sourcePanel203Checkpoint_zero
    sourcePanel203Chunks_checked).trans hlast

theorem sourcePanel203_stream_passes :
    sourcePanelCheck ⟨203, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨203, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨203, by decide⟩)
    sourcePanel203Candidate_stream).trans sourcePanel203Candidate_passes

end ReciprocalXi

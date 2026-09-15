import ProofWorkspace.Final.SourcePanel294BoundsFull
import ProofWorkspace.Final.SourcePanel294ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel294Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨294, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel294Candidate := by
  have hlast : (sourcePanel294Checkpoint 54).2 = sourcePanel294Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨294, by decide⟩ sourcePanel294Seed
    sourcePanel294Checkpoint sourcePanel294Seed_checked sourcePanel294Checkpoint_zero
    sourcePanel294Chunks_checked).trans hlast

theorem sourcePanel294_stream_passes :
    sourcePanelCheck ⟨294, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨294, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨294, by decide⟩)
    sourcePanel294Candidate_stream).trans sourcePanel294Candidate_passes

end ReciprocalXi

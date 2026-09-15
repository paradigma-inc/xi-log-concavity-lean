import ProofWorkspace.Final.SourcePanel14BoundsFull
import ProofWorkspace.Final.SourcePanel14ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel14Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨14, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel14Candidate := by
  have hlast : (sourcePanel14Checkpoint 54).2 = sourcePanel14Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨14, by decide⟩ sourcePanel14Seed
    sourcePanel14Checkpoint sourcePanel14Seed_checked sourcePanel14Checkpoint_zero
    sourcePanel14Chunks_checked).trans hlast

theorem sourcePanel14_stream_passes :
    sourcePanelCheck ⟨14, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨14, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨14, by decide⟩)
    sourcePanel14Candidate_stream).trans sourcePanel14Candidate_passes

end ReciprocalXi

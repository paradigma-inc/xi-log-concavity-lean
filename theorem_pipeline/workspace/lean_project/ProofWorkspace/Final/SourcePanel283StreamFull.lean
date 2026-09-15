import ProofWorkspace.Final.SourcePanel283BoundsFull
import ProofWorkspace.Final.SourcePanel283ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel283Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨283, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel283Candidate := by
  have hlast : (sourcePanel283Checkpoint 54).2 = sourcePanel283Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨283, by decide⟩ sourcePanel283Seed
    sourcePanel283Checkpoint sourcePanel283Seed_checked sourcePanel283Checkpoint_zero
    sourcePanel283Chunks_checked).trans hlast

theorem sourcePanel283_stream_passes :
    sourcePanelCheck ⟨283, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨283, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨283, by decide⟩)
    sourcePanel283Candidate_stream).trans sourcePanel283Candidate_passes

end ReciprocalXi

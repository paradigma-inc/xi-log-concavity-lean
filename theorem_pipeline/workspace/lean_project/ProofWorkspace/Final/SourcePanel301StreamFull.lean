import ProofWorkspace.Final.SourcePanel301BoundsFull
import ProofWorkspace.Final.SourcePanel301ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel301Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨301, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel301Candidate := by
  have hlast : (sourcePanel301Checkpoint 54).2 = sourcePanel301Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨301, by decide⟩ sourcePanel301Seed
    sourcePanel301Checkpoint sourcePanel301Seed_checked sourcePanel301Checkpoint_zero
    sourcePanel301Chunks_checked).trans hlast

theorem sourcePanel301_stream_passes :
    sourcePanelCheck ⟨301, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨301, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨301, by decide⟩)
    sourcePanel301Candidate_stream).trans sourcePanel301Candidate_passes

end ReciprocalXi

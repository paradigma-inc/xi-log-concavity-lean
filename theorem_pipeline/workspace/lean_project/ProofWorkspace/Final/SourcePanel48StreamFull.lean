import ProofWorkspace.Final.SourcePanel48BoundsFull
import ProofWorkspace.Final.SourcePanel48ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel48Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨48, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel48Candidate := by
  have hlast : (sourcePanel48Checkpoint 54).2 = sourcePanel48Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨48, by decide⟩ sourcePanel48Seed
    sourcePanel48Checkpoint sourcePanel48Seed_checked sourcePanel48Checkpoint_zero
    sourcePanel48Chunks_checked).trans hlast

theorem sourcePanel48_stream_passes :
    sourcePanelCheck ⟨48, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨48, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨48, by decide⟩)
    sourcePanel48Candidate_stream).trans sourcePanel48Candidate_passes

end ReciprocalXi

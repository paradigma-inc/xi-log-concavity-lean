import ProofWorkspace.Final.SourcePanel114BoundsFull
import ProofWorkspace.Final.SourcePanel114ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel114Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨114, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel114Candidate := by
  have hlast : (sourcePanel114Checkpoint 54).2 = sourcePanel114Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨114, by decide⟩ sourcePanel114Seed
    sourcePanel114Checkpoint sourcePanel114Seed_checked sourcePanel114Checkpoint_zero
    sourcePanel114Chunks_checked).trans hlast

theorem sourcePanel114_stream_passes :
    sourcePanelCheck ⟨114, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨114, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨114, by decide⟩)
    sourcePanel114Candidate_stream).trans sourcePanel114Candidate_passes

end ReciprocalXi

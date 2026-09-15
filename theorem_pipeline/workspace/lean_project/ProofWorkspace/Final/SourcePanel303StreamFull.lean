import ProofWorkspace.Final.SourcePanel303BoundsFull
import ProofWorkspace.Final.SourcePanel303ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel303Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨303, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel303Candidate := by
  have hlast : (sourcePanel303Checkpoint 54).2 = sourcePanel303Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨303, by decide⟩ sourcePanel303Seed
    sourcePanel303Checkpoint sourcePanel303Seed_checked sourcePanel303Checkpoint_zero
    sourcePanel303Chunks_checked).trans hlast

theorem sourcePanel303_stream_passes :
    sourcePanelCheck ⟨303, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨303, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨303, by decide⟩)
    sourcePanel303Candidate_stream).trans sourcePanel303Candidate_passes

end ReciprocalXi

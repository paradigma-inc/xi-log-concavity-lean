import ProofWorkspace.Final.SourcePanel85BoundsFull
import ProofWorkspace.Final.SourcePanel85ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel85Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨85, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel85Candidate := by
  have hlast : (sourcePanel85Checkpoint 54).2 = sourcePanel85Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨85, by decide⟩ sourcePanel85Seed
    sourcePanel85Checkpoint sourcePanel85Seed_checked sourcePanel85Checkpoint_zero
    sourcePanel85Chunks_checked).trans hlast

theorem sourcePanel85_stream_passes :
    sourcePanelCheck ⟨85, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨85, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨85, by decide⟩)
    sourcePanel85Candidate_stream).trans sourcePanel85Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel310BoundsFull
import ProofWorkspace.Final.SourcePanel310ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel310Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨310, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel310Candidate := by
  have hlast : (sourcePanel310Checkpoint 54).2 = sourcePanel310Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨310, by decide⟩ sourcePanel310Seed
    sourcePanel310Checkpoint sourcePanel310Seed_checked sourcePanel310Checkpoint_zero
    sourcePanel310Chunks_checked).trans hlast

theorem sourcePanel310_stream_passes :
    sourcePanelCheck ⟨310, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨310, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨310, by decide⟩)
    sourcePanel310Candidate_stream).trans sourcePanel310Candidate_passes

end ReciprocalXi

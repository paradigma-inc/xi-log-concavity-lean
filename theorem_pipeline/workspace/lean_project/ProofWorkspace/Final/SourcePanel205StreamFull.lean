import ProofWorkspace.Final.SourcePanel205BoundsFull
import ProofWorkspace.Final.SourcePanel205ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel205Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨205, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel205Candidate := by
  have hlast : (sourcePanel205Checkpoint 54).2 = sourcePanel205Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨205, by decide⟩ sourcePanel205Seed
    sourcePanel205Checkpoint sourcePanel205Seed_checked sourcePanel205Checkpoint_zero
    sourcePanel205Chunks_checked).trans hlast

theorem sourcePanel205_stream_passes :
    sourcePanelCheck ⟨205, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨205, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨205, by decide⟩)
    sourcePanel205Candidate_stream).trans sourcePanel205Candidate_passes

end ReciprocalXi

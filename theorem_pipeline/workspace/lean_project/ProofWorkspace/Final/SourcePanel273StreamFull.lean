import ProofWorkspace.Final.SourcePanel273BoundsFull
import ProofWorkspace.Final.SourcePanel273ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel273Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨273, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel273Candidate := by
  have hlast : (sourcePanel273Checkpoint 54).2 = sourcePanel273Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨273, by decide⟩ sourcePanel273Seed
    sourcePanel273Checkpoint sourcePanel273Seed_checked sourcePanel273Checkpoint_zero
    sourcePanel273Chunks_checked).trans hlast

theorem sourcePanel273_stream_passes :
    sourcePanelCheck ⟨273, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨273, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨273, by decide⟩)
    sourcePanel273Candidate_stream).trans sourcePanel273Candidate_passes

end ReciprocalXi

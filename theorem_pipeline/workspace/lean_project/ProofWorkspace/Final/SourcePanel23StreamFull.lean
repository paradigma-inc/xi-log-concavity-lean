import ProofWorkspace.Final.SourcePanel23BoundsFull
import ProofWorkspace.Final.SourcePanel23ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel23Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨23, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel23Candidate := by
  have hlast : (sourcePanel23Checkpoint 54).2 = sourcePanel23Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨23, by decide⟩ sourcePanel23Seed
    sourcePanel23Checkpoint sourcePanel23Seed_checked sourcePanel23Checkpoint_zero
    sourcePanel23Chunks_checked).trans hlast

theorem sourcePanel23_stream_passes :
    sourcePanelCheck ⟨23, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨23, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨23, by decide⟩)
    sourcePanel23Candidate_stream).trans sourcePanel23Candidate_passes

end ReciprocalXi

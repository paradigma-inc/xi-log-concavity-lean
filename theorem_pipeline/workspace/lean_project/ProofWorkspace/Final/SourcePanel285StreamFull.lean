import ProofWorkspace.Final.SourcePanel285BoundsFull
import ProofWorkspace.Final.SourcePanel285ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel285Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨285, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel285Candidate := by
  have hlast : (sourcePanel285Checkpoint 54).2 = sourcePanel285Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨285, by decide⟩ sourcePanel285Seed
    sourcePanel285Checkpoint sourcePanel285Seed_checked sourcePanel285Checkpoint_zero
    sourcePanel285Chunks_checked).trans hlast

theorem sourcePanel285_stream_passes :
    sourcePanelCheck ⟨285, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨285, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨285, by decide⟩)
    sourcePanel285Candidate_stream).trans sourcePanel285Candidate_passes

end ReciprocalXi

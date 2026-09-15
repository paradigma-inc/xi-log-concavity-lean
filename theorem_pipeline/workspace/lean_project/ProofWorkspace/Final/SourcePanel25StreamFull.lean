import ProofWorkspace.Final.SourcePanel25BoundsFull
import ProofWorkspace.Final.SourcePanel25ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel25Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨25, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel25Candidate := by
  have hlast : (sourcePanel25Checkpoint 54).2 = sourcePanel25Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨25, by decide⟩ sourcePanel25Seed
    sourcePanel25Checkpoint sourcePanel25Seed_checked sourcePanel25Checkpoint_zero
    sourcePanel25Chunks_checked).trans hlast

theorem sourcePanel25_stream_passes :
    sourcePanelCheck ⟨25, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨25, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨25, by decide⟩)
    sourcePanel25Candidate_stream).trans sourcePanel25Candidate_passes

end ReciprocalXi

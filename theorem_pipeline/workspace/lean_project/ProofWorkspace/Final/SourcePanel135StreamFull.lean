import ProofWorkspace.Final.SourcePanel135BoundsFull
import ProofWorkspace.Final.SourcePanel135ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel135Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨135, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel135Candidate := by
  have hlast : (sourcePanel135Checkpoint 54).2 = sourcePanel135Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨135, by decide⟩ sourcePanel135Seed
    sourcePanel135Checkpoint sourcePanel135Seed_checked sourcePanel135Checkpoint_zero
    sourcePanel135Chunks_checked).trans hlast

theorem sourcePanel135_stream_passes :
    sourcePanelCheck ⟨135, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨135, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨135, by decide⟩)
    sourcePanel135Candidate_stream).trans sourcePanel135Candidate_passes

end ReciprocalXi

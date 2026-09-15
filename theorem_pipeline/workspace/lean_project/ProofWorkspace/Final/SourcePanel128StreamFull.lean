import ProofWorkspace.Final.SourcePanel128BoundsFull
import ProofWorkspace.Final.SourcePanel128ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel128Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨128, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel128Candidate := by
  have hlast : (sourcePanel128Checkpoint 54).2 = sourcePanel128Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨128, by decide⟩ sourcePanel128Seed
    sourcePanel128Checkpoint sourcePanel128Seed_checked sourcePanel128Checkpoint_zero
    sourcePanel128Chunks_checked).trans hlast

theorem sourcePanel128_stream_passes :
    sourcePanelCheck ⟨128, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨128, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨128, by decide⟩)
    sourcePanel128Candidate_stream).trans sourcePanel128Candidate_passes

end ReciprocalXi

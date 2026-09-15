import ProofWorkspace.Final.SourcePanel299BoundsFull
import ProofWorkspace.Final.SourcePanel299ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel299Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨299, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel299Candidate := by
  have hlast : (sourcePanel299Checkpoint 54).2 = sourcePanel299Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨299, by decide⟩ sourcePanel299Seed
    sourcePanel299Checkpoint sourcePanel299Seed_checked sourcePanel299Checkpoint_zero
    sourcePanel299Chunks_checked).trans hlast

theorem sourcePanel299_stream_passes :
    sourcePanelCheck ⟨299, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨299, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨299, by decide⟩)
    sourcePanel299Candidate_stream).trans sourcePanel299Candidate_passes

end ReciprocalXi

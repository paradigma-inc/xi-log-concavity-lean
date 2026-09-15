import ProofWorkspace.Final.SourcePanel197BoundsFull
import ProofWorkspace.Final.SourcePanel197ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel197Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨197, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel197Candidate := by
  have hlast : (sourcePanel197Checkpoint 54).2 = sourcePanel197Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨197, by decide⟩ sourcePanel197Seed
    sourcePanel197Checkpoint sourcePanel197Seed_checked sourcePanel197Checkpoint_zero
    sourcePanel197Chunks_checked).trans hlast

theorem sourcePanel197_stream_passes :
    sourcePanelCheck ⟨197, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨197, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨197, by decide⟩)
    sourcePanel197Candidate_stream).trans sourcePanel197Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel311BoundsFull
import ProofWorkspace.Final.SourcePanel311ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel311Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨311, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel311Candidate := by
  have hlast : (sourcePanel311Checkpoint 54).2 = sourcePanel311Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨311, by decide⟩ sourcePanel311Seed
    sourcePanel311Checkpoint sourcePanel311Seed_checked sourcePanel311Checkpoint_zero
    sourcePanel311Chunks_checked).trans hlast

theorem sourcePanel311_stream_passes :
    sourcePanelCheck ⟨311, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨311, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨311, by decide⟩)
    sourcePanel311Candidate_stream).trans sourcePanel311Candidate_passes

end ReciprocalXi

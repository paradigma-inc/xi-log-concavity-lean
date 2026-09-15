import ProofWorkspace.Final.SourcePanel210BoundsFull
import ProofWorkspace.Final.SourcePanel210ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel210Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨210, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel210Candidate := by
  have hlast : (sourcePanel210Checkpoint 54).2 = sourcePanel210Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨210, by decide⟩ sourcePanel210Seed
    sourcePanel210Checkpoint sourcePanel210Seed_checked sourcePanel210Checkpoint_zero
    sourcePanel210Chunks_checked).trans hlast

theorem sourcePanel210_stream_passes :
    sourcePanelCheck ⟨210, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨210, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨210, by decide⟩)
    sourcePanel210Candidate_stream).trans sourcePanel210Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel252BoundsFull
import ProofWorkspace.Final.SourcePanel252ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel252Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨252, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel252Candidate := by
  have hlast : (sourcePanel252Checkpoint 54).2 = sourcePanel252Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨252, by decide⟩ sourcePanel252Seed
    sourcePanel252Checkpoint sourcePanel252Seed_checked sourcePanel252Checkpoint_zero
    sourcePanel252Chunks_checked).trans hlast

theorem sourcePanel252_stream_passes :
    sourcePanelCheck ⟨252, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨252, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨252, by decide⟩)
    sourcePanel252Candidate_stream).trans sourcePanel252Candidate_passes

end ReciprocalXi

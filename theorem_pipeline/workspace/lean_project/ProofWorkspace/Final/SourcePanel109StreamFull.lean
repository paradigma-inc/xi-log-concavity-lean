import ProofWorkspace.Final.SourcePanel109BoundsFull
import ProofWorkspace.Final.SourcePanel109ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel109Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨109, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel109Candidate := by
  have hlast : (sourcePanel109Checkpoint 54).2 = sourcePanel109Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨109, by decide⟩ sourcePanel109Seed
    sourcePanel109Checkpoint sourcePanel109Seed_checked sourcePanel109Checkpoint_zero
    sourcePanel109Chunks_checked).trans hlast

theorem sourcePanel109_stream_passes :
    sourcePanelCheck ⟨109, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨109, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨109, by decide⟩)
    sourcePanel109Candidate_stream).trans sourcePanel109Candidate_passes

end ReciprocalXi

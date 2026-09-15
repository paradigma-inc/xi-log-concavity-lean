import ProofWorkspace.Final.SourcePanel211BoundsFull
import ProofWorkspace.Final.SourcePanel211ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel211Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨211, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel211Candidate := by
  have hlast : (sourcePanel211Checkpoint 54).2 = sourcePanel211Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨211, by decide⟩ sourcePanel211Seed
    sourcePanel211Checkpoint sourcePanel211Seed_checked sourcePanel211Checkpoint_zero
    sourcePanel211Chunks_checked).trans hlast

theorem sourcePanel211_stream_passes :
    sourcePanelCheck ⟨211, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨211, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨211, by decide⟩)
    sourcePanel211Candidate_stream).trans sourcePanel211Candidate_passes

end ReciprocalXi

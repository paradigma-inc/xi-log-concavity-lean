import ProofWorkspace.Final.SourcePanel129BoundsFull
import ProofWorkspace.Final.SourcePanel129ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel129Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨129, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel129Candidate := by
  have hlast : (sourcePanel129Checkpoint 54).2 = sourcePanel129Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨129, by decide⟩ sourcePanel129Seed
    sourcePanel129Checkpoint sourcePanel129Seed_checked sourcePanel129Checkpoint_zero
    sourcePanel129Chunks_checked).trans hlast

theorem sourcePanel129_stream_passes :
    sourcePanelCheck ⟨129, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨129, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨129, by decide⟩)
    sourcePanel129Candidate_stream).trans sourcePanel129Candidate_passes

end ReciprocalXi

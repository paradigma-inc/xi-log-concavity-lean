import ProofWorkspace.Final.SourcePanel236BoundsFull
import ProofWorkspace.Final.SourcePanel236ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel236Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨236, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel236Candidate := by
  have hlast : (sourcePanel236Checkpoint 54).2 = sourcePanel236Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨236, by decide⟩ sourcePanel236Seed
    sourcePanel236Checkpoint sourcePanel236Seed_checked sourcePanel236Checkpoint_zero
    sourcePanel236Chunks_checked).trans hlast

theorem sourcePanel236_stream_passes :
    sourcePanelCheck ⟨236, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨236, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨236, by decide⟩)
    sourcePanel236Candidate_stream).trans sourcePanel236Candidate_passes

end ReciprocalXi

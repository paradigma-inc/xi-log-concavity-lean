import ProofWorkspace.Final.SourcePanel118BoundsFull
import ProofWorkspace.Final.SourcePanel118ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel118Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨118, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel118Candidate := by
  have hlast : (sourcePanel118Checkpoint 54).2 = sourcePanel118Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨118, by decide⟩ sourcePanel118Seed
    sourcePanel118Checkpoint sourcePanel118Seed_checked sourcePanel118Checkpoint_zero
    sourcePanel118Chunks_checked).trans hlast

theorem sourcePanel118_stream_passes :
    sourcePanelCheck ⟨118, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨118, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨118, by decide⟩)
    sourcePanel118Candidate_stream).trans sourcePanel118Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel184BoundsFull
import ProofWorkspace.Final.SourcePanel184ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel184Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨184, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel184Candidate := by
  have hlast : (sourcePanel184Checkpoint 54).2 = sourcePanel184Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨184, by decide⟩ sourcePanel184Seed
    sourcePanel184Checkpoint sourcePanel184Seed_checked sourcePanel184Checkpoint_zero
    sourcePanel184Chunks_checked).trans hlast

theorem sourcePanel184_stream_passes :
    sourcePanelCheck ⟨184, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨184, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨184, by decide⟩)
    sourcePanel184Candidate_stream).trans sourcePanel184Candidate_passes

end ReciprocalXi

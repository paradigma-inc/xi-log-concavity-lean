import ProofWorkspace.Final.SourcePanel188BoundsFull
import ProofWorkspace.Final.SourcePanel188ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel188Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨188, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel188Candidate := by
  have hlast : (sourcePanel188Checkpoint 54).2 = sourcePanel188Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨188, by decide⟩ sourcePanel188Seed
    sourcePanel188Checkpoint sourcePanel188Seed_checked sourcePanel188Checkpoint_zero
    sourcePanel188Chunks_checked).trans hlast

theorem sourcePanel188_stream_passes :
    sourcePanelCheck ⟨188, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨188, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨188, by decide⟩)
    sourcePanel188Candidate_stream).trans sourcePanel188Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel147BoundsFull
import ProofWorkspace.Final.SourcePanel147ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel147Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨147, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel147Candidate := by
  have hlast : (sourcePanel147Checkpoint 54).2 = sourcePanel147Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨147, by decide⟩ sourcePanel147Seed
    sourcePanel147Checkpoint sourcePanel147Seed_checked sourcePanel147Checkpoint_zero
    sourcePanel147Chunks_checked).trans hlast

theorem sourcePanel147_stream_passes :
    sourcePanelCheck ⟨147, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨147, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨147, by decide⟩)
    sourcePanel147Candidate_stream).trans sourcePanel147Candidate_passes

end ReciprocalXi

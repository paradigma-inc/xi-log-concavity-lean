import ProofWorkspace.Final.SourcePanel156BoundsFull
import ProofWorkspace.Final.SourcePanel156ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel156Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨156, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel156Candidate := by
  have hlast : (sourcePanel156Checkpoint 54).2 = sourcePanel156Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨156, by decide⟩ sourcePanel156Seed
    sourcePanel156Checkpoint sourcePanel156Seed_checked sourcePanel156Checkpoint_zero
    sourcePanel156Chunks_checked).trans hlast

theorem sourcePanel156_stream_passes :
    sourcePanelCheck ⟨156, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨156, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨156, by decide⟩)
    sourcePanel156Candidate_stream).trans sourcePanel156Candidate_passes

end ReciprocalXi

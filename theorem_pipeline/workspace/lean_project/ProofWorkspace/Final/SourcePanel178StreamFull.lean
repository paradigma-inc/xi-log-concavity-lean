import ProofWorkspace.Final.SourcePanel178BoundsFull
import ProofWorkspace.Final.SourcePanel178ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel178Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨178, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel178Candidate := by
  have hlast : (sourcePanel178Checkpoint 54).2 = sourcePanel178Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨178, by decide⟩ sourcePanel178Seed
    sourcePanel178Checkpoint sourcePanel178Seed_checked sourcePanel178Checkpoint_zero
    sourcePanel178Chunks_checked).trans hlast

theorem sourcePanel178_stream_passes :
    sourcePanelCheck ⟨178, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨178, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨178, by decide⟩)
    sourcePanel178Candidate_stream).trans sourcePanel178Candidate_passes

end ReciprocalXi

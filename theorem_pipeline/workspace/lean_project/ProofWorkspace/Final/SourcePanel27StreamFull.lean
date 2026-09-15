import ProofWorkspace.Final.SourcePanel27BoundsFull
import ProofWorkspace.Final.SourcePanel27ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel27Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨27, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel27Candidate := by
  have hlast : (sourcePanel27Checkpoint 54).2 = sourcePanel27Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨27, by decide⟩ sourcePanel27Seed
    sourcePanel27Checkpoint sourcePanel27Seed_checked sourcePanel27Checkpoint_zero
    sourcePanel27Chunks_checked).trans hlast

theorem sourcePanel27_stream_passes :
    sourcePanelCheck ⟨27, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨27, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨27, by decide⟩)
    sourcePanel27Candidate_stream).trans sourcePanel27Candidate_passes

end ReciprocalXi

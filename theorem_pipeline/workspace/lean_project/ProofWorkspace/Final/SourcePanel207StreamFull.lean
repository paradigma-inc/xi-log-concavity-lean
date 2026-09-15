import ProofWorkspace.Final.SourcePanel207BoundsFull
import ProofWorkspace.Final.SourcePanel207ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel207Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨207, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel207Candidate := by
  have hlast : (sourcePanel207Checkpoint 54).2 = sourcePanel207Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨207, by decide⟩ sourcePanel207Seed
    sourcePanel207Checkpoint sourcePanel207Seed_checked sourcePanel207Checkpoint_zero
    sourcePanel207Chunks_checked).trans hlast

theorem sourcePanel207_stream_passes :
    sourcePanelCheck ⟨207, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨207, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨207, by decide⟩)
    sourcePanel207Candidate_stream).trans sourcePanel207Candidate_passes

end ReciprocalXi

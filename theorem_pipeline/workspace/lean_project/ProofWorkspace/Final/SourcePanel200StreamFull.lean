import ProofWorkspace.Final.SourcePanel200BoundsFull
import ProofWorkspace.Final.SourcePanel200ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel200Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨200, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel200Candidate := by
  have hlast : (sourcePanel200Checkpoint 54).2 = sourcePanel200Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨200, by decide⟩ sourcePanel200Seed
    sourcePanel200Checkpoint sourcePanel200Seed_checked sourcePanel200Checkpoint_zero
    sourcePanel200Chunks_checked).trans hlast

theorem sourcePanel200_stream_passes :
    sourcePanelCheck ⟨200, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨200, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨200, by decide⟩)
    sourcePanel200Candidate_stream).trans sourcePanel200Candidate_passes

end ReciprocalXi

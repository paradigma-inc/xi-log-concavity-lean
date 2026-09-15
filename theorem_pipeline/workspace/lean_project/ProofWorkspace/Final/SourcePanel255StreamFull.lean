import ProofWorkspace.Final.SourcePanel255BoundsFull
import ProofWorkspace.Final.SourcePanel255ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel255Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨255, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel255Candidate := by
  have hlast : (sourcePanel255Checkpoint 54).2 = sourcePanel255Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨255, by decide⟩ sourcePanel255Seed
    sourcePanel255Checkpoint sourcePanel255Seed_checked sourcePanel255Checkpoint_zero
    sourcePanel255Chunks_checked).trans hlast

theorem sourcePanel255_stream_passes :
    sourcePanelCheck ⟨255, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨255, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨255, by decide⟩)
    sourcePanel255Candidate_stream).trans sourcePanel255Candidate_passes

end ReciprocalXi

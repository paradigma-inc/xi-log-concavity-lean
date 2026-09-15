import ProofWorkspace.Final.SourcePanel271BoundsFull
import ProofWorkspace.Final.SourcePanel271ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel271Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨271, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel271Candidate := by
  have hlast : (sourcePanel271Checkpoint 54).2 = sourcePanel271Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨271, by decide⟩ sourcePanel271Seed
    sourcePanel271Checkpoint sourcePanel271Seed_checked sourcePanel271Checkpoint_zero
    sourcePanel271Chunks_checked).trans hlast

theorem sourcePanel271_stream_passes :
    sourcePanelCheck ⟨271, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨271, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨271, by decide⟩)
    sourcePanel271Candidate_stream).trans sourcePanel271Candidate_passes

end ReciprocalXi

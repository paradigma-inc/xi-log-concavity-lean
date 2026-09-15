import ProofWorkspace.Final.SourcePanel94BoundsFull
import ProofWorkspace.Final.SourcePanel94ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel94Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨94, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel94Candidate := by
  have hlast : (sourcePanel94Checkpoint 54).2 = sourcePanel94Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨94, by decide⟩ sourcePanel94Seed
    sourcePanel94Checkpoint sourcePanel94Seed_checked sourcePanel94Checkpoint_zero
    sourcePanel94Chunks_checked).trans hlast

theorem sourcePanel94_stream_passes :
    sourcePanelCheck ⟨94, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨94, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨94, by decide⟩)
    sourcePanel94Candidate_stream).trans sourcePanel94Candidate_passes

end ReciprocalXi

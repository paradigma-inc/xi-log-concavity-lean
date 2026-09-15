import ProofWorkspace.Final.SourcePanel98BoundsFull
import ProofWorkspace.Final.SourcePanel98ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel98Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨98, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel98Candidate := by
  have hlast : (sourcePanel98Checkpoint 54).2 = sourcePanel98Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨98, by decide⟩ sourcePanel98Seed
    sourcePanel98Checkpoint sourcePanel98Seed_checked sourcePanel98Checkpoint_zero
    sourcePanel98Chunks_checked).trans hlast

theorem sourcePanel98_stream_passes :
    sourcePanelCheck ⟨98, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨98, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨98, by decide⟩)
    sourcePanel98Candidate_stream).trans sourcePanel98Candidate_passes

end ReciprocalXi

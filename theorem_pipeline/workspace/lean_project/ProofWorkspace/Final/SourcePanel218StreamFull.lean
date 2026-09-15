import ProofWorkspace.Final.SourcePanel218BoundsFull
import ProofWorkspace.Final.SourcePanel218ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel218Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨218, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel218Candidate := by
  have hlast : (sourcePanel218Checkpoint 54).2 = sourcePanel218Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨218, by decide⟩ sourcePanel218Seed
    sourcePanel218Checkpoint sourcePanel218Seed_checked sourcePanel218Checkpoint_zero
    sourcePanel218Chunks_checked).trans hlast

theorem sourcePanel218_stream_passes :
    sourcePanelCheck ⟨218, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨218, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨218, by decide⟩)
    sourcePanel218Candidate_stream).trans sourcePanel218Candidate_passes

end ReciprocalXi

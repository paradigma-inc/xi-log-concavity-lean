import ProofWorkspace.Final.SourcePanel107BoundsFull
import ProofWorkspace.Final.SourcePanel107ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel107Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨107, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel107Candidate := by
  have hlast : (sourcePanel107Checkpoint 54).2 = sourcePanel107Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨107, by decide⟩ sourcePanel107Seed
    sourcePanel107Checkpoint sourcePanel107Seed_checked sourcePanel107Checkpoint_zero
    sourcePanel107Chunks_checked).trans hlast

theorem sourcePanel107_stream_passes :
    sourcePanelCheck ⟨107, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨107, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨107, by decide⟩)
    sourcePanel107Candidate_stream).trans sourcePanel107Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel155BoundsFull
import ProofWorkspace.Final.SourcePanel155ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel155Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨155, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel155Candidate := by
  have hlast : (sourcePanel155Checkpoint 54).2 = sourcePanel155Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨155, by decide⟩ sourcePanel155Seed
    sourcePanel155Checkpoint sourcePanel155Seed_checked sourcePanel155Checkpoint_zero
    sourcePanel155Chunks_checked).trans hlast

theorem sourcePanel155_stream_passes :
    sourcePanelCheck ⟨155, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨155, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨155, by decide⟩)
    sourcePanel155Candidate_stream).trans sourcePanel155Candidate_passes

end ReciprocalXi

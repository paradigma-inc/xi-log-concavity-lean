import ProofWorkspace.Final.SourcePanel194BoundsFull
import ProofWorkspace.Final.SourcePanel194ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel194Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨194, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel194Candidate := by
  have hlast : (sourcePanel194Checkpoint 54).2 = sourcePanel194Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨194, by decide⟩ sourcePanel194Seed
    sourcePanel194Checkpoint sourcePanel194Seed_checked sourcePanel194Checkpoint_zero
    sourcePanel194Chunks_checked).trans hlast

theorem sourcePanel194_stream_passes :
    sourcePanelCheck ⟨194, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨194, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨194, by decide⟩)
    sourcePanel194Candidate_stream).trans sourcePanel194Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel28BoundsFull
import ProofWorkspace.Final.SourcePanel28ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel28Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨28, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel28Candidate := by
  have hlast : (sourcePanel28Checkpoint 54).2 = sourcePanel28Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨28, by decide⟩ sourcePanel28Seed
    sourcePanel28Checkpoint sourcePanel28Seed_checked sourcePanel28Checkpoint_zero
    sourcePanel28Chunks_checked).trans hlast

theorem sourcePanel28_stream_passes :
    sourcePanelCheck ⟨28, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨28, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨28, by decide⟩)
    sourcePanel28Candidate_stream).trans sourcePanel28Candidate_passes

end ReciprocalXi

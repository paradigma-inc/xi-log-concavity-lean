import ProofWorkspace.Final.SourcePanel175BoundsFull
import ProofWorkspace.Final.SourcePanel175ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel175Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨175, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel175Candidate := by
  have hlast : (sourcePanel175Checkpoint 54).2 = sourcePanel175Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨175, by decide⟩ sourcePanel175Seed
    sourcePanel175Checkpoint sourcePanel175Seed_checked sourcePanel175Checkpoint_zero
    sourcePanel175Chunks_checked).trans hlast

theorem sourcePanel175_stream_passes :
    sourcePanelCheck ⟨175, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨175, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨175, by decide⟩)
    sourcePanel175Candidate_stream).trans sourcePanel175Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel198BoundsFull
import ProofWorkspace.Final.SourcePanel198ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel198Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨198, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel198Candidate := by
  have hlast : (sourcePanel198Checkpoint 54).2 = sourcePanel198Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨198, by decide⟩ sourcePanel198Seed
    sourcePanel198Checkpoint sourcePanel198Seed_checked sourcePanel198Checkpoint_zero
    sourcePanel198Chunks_checked).trans hlast

theorem sourcePanel198_stream_passes :
    sourcePanelCheck ⟨198, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨198, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨198, by decide⟩)
    sourcePanel198Candidate_stream).trans sourcePanel198Candidate_passes

end ReciprocalXi

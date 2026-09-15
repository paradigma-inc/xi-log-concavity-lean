import ProofWorkspace.Final.SourcePanel126BoundsFull
import ProofWorkspace.Final.SourcePanel126ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel126Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨126, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel126Candidate := by
  have hlast : (sourcePanel126Checkpoint 54).2 = sourcePanel126Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨126, by decide⟩ sourcePanel126Seed
    sourcePanel126Checkpoint sourcePanel126Seed_checked sourcePanel126Checkpoint_zero
    sourcePanel126Chunks_checked).trans hlast

theorem sourcePanel126_stream_passes :
    sourcePanelCheck ⟨126, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨126, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨126, by decide⟩)
    sourcePanel126Candidate_stream).trans sourcePanel126Candidate_passes

end ReciprocalXi

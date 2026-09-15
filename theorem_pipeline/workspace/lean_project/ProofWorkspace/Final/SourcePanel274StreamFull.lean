import ProofWorkspace.Final.SourcePanel274BoundsFull
import ProofWorkspace.Final.SourcePanel274ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel274Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨274, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel274Candidate := by
  have hlast : (sourcePanel274Checkpoint 54).2 = sourcePanel274Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨274, by decide⟩ sourcePanel274Seed
    sourcePanel274Checkpoint sourcePanel274Seed_checked sourcePanel274Checkpoint_zero
    sourcePanel274Chunks_checked).trans hlast

theorem sourcePanel274_stream_passes :
    sourcePanelCheck ⟨274, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨274, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨274, by decide⟩)
    sourcePanel274Candidate_stream).trans sourcePanel274Candidate_passes

end ReciprocalXi

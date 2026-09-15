import ProofWorkspace.Final.SourcePanel40BoundsFull
import ProofWorkspace.Final.SourcePanel40ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel40Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨40, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel40Candidate := by
  have hlast : (sourcePanel40Checkpoint 54).2 = sourcePanel40Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨40, by decide⟩ sourcePanel40Seed
    sourcePanel40Checkpoint sourcePanel40Seed_checked sourcePanel40Checkpoint_zero
    sourcePanel40Chunks_checked).trans hlast

theorem sourcePanel40_stream_passes :
    sourcePanelCheck ⟨40, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨40, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨40, by decide⟩)
    sourcePanel40Candidate_stream).trans sourcePanel40Candidate_passes

end ReciprocalXi

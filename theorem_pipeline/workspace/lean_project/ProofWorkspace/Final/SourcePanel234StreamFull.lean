import ProofWorkspace.Final.SourcePanel234BoundsFull
import ProofWorkspace.Final.SourcePanel234ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel234Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨234, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel234Candidate := by
  have hlast : (sourcePanel234Checkpoint 54).2 = sourcePanel234Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨234, by decide⟩ sourcePanel234Seed
    sourcePanel234Checkpoint sourcePanel234Seed_checked sourcePanel234Checkpoint_zero
    sourcePanel234Chunks_checked).trans hlast

theorem sourcePanel234_stream_passes :
    sourcePanelCheck ⟨234, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨234, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨234, by decide⟩)
    sourcePanel234Candidate_stream).trans sourcePanel234Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel296BoundsFull
import ProofWorkspace.Final.SourcePanel296ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel296Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨296, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel296Candidate := by
  have hlast : (sourcePanel296Checkpoint 54).2 = sourcePanel296Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨296, by decide⟩ sourcePanel296Seed
    sourcePanel296Checkpoint sourcePanel296Seed_checked sourcePanel296Checkpoint_zero
    sourcePanel296Chunks_checked).trans hlast

theorem sourcePanel296_stream_passes :
    sourcePanelCheck ⟨296, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨296, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨296, by decide⟩)
    sourcePanel296Candidate_stream).trans sourcePanel296Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel102BoundsFull
import ProofWorkspace.Final.SourcePanel102ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel102Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨102, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel102Candidate := by
  have hlast : (sourcePanel102Checkpoint 54).2 = sourcePanel102Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨102, by decide⟩ sourcePanel102Seed
    sourcePanel102Checkpoint sourcePanel102Seed_checked sourcePanel102Checkpoint_zero
    sourcePanel102Chunks_checked).trans hlast

theorem sourcePanel102_stream_passes :
    sourcePanelCheck ⟨102, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨102, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨102, by decide⟩)
    sourcePanel102Candidate_stream).trans sourcePanel102Candidate_passes

end ReciprocalXi

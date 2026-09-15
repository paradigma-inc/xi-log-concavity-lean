import ProofWorkspace.Final.SourcePanel199BoundsFull
import ProofWorkspace.Final.SourcePanel199ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel199Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨199, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel199Candidate := by
  have hlast : (sourcePanel199Checkpoint 54).2 = sourcePanel199Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨199, by decide⟩ sourcePanel199Seed
    sourcePanel199Checkpoint sourcePanel199Seed_checked sourcePanel199Checkpoint_zero
    sourcePanel199Chunks_checked).trans hlast

theorem sourcePanel199_stream_passes :
    sourcePanelCheck ⟨199, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨199, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨199, by decide⟩)
    sourcePanel199Candidate_stream).trans sourcePanel199Candidate_passes

end ReciprocalXi

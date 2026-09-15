import ProofWorkspace.Final.SourcePanel124BoundsFull
import ProofWorkspace.Final.SourcePanel124ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel124Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨124, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel124Candidate := by
  have hlast : (sourcePanel124Checkpoint 54).2 = sourcePanel124Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨124, by decide⟩ sourcePanel124Seed
    sourcePanel124Checkpoint sourcePanel124Seed_checked sourcePanel124Checkpoint_zero
    sourcePanel124Chunks_checked).trans hlast

theorem sourcePanel124_stream_passes :
    sourcePanelCheck ⟨124, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨124, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨124, by decide⟩)
    sourcePanel124Candidate_stream).trans sourcePanel124Candidate_passes

end ReciprocalXi

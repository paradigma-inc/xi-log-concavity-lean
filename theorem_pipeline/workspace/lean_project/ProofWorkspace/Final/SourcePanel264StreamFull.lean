import ProofWorkspace.Final.SourcePanel264BoundsFull
import ProofWorkspace.Final.SourcePanel264ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel264Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨264, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel264Candidate := by
  have hlast : (sourcePanel264Checkpoint 54).2 = sourcePanel264Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨264, by decide⟩ sourcePanel264Seed
    sourcePanel264Checkpoint sourcePanel264Seed_checked sourcePanel264Checkpoint_zero
    sourcePanel264Chunks_checked).trans hlast

theorem sourcePanel264_stream_passes :
    sourcePanelCheck ⟨264, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨264, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨264, by decide⟩)
    sourcePanel264Candidate_stream).trans sourcePanel264Candidate_passes

end ReciprocalXi

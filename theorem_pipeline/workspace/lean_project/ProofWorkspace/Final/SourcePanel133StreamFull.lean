import ProofWorkspace.Final.SourcePanel133BoundsFull
import ProofWorkspace.Final.SourcePanel133ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel133Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨133, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel133Candidate := by
  have hlast : (sourcePanel133Checkpoint 54).2 = sourcePanel133Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨133, by decide⟩ sourcePanel133Seed
    sourcePanel133Checkpoint sourcePanel133Seed_checked sourcePanel133Checkpoint_zero
    sourcePanel133Chunks_checked).trans hlast

theorem sourcePanel133_stream_passes :
    sourcePanelCheck ⟨133, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨133, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨133, by decide⟩)
    sourcePanel133Candidate_stream).trans sourcePanel133Candidate_passes

end ReciprocalXi

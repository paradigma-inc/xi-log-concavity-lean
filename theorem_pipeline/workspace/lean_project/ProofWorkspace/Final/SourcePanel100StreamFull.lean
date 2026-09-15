import ProofWorkspace.Final.SourcePanel100BoundsFull
import ProofWorkspace.Final.SourcePanel100ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel100Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨100, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel100Candidate := by
  have hlast : (sourcePanel100Checkpoint 54).2 = sourcePanel100Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨100, by decide⟩ sourcePanel100Seed
    sourcePanel100Checkpoint sourcePanel100Seed_checked sourcePanel100Checkpoint_zero
    sourcePanel100Chunks_checked).trans hlast

theorem sourcePanel100_stream_passes :
    sourcePanelCheck ⟨100, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨100, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨100, by decide⟩)
    sourcePanel100Candidate_stream).trans sourcePanel100Candidate_passes

end ReciprocalXi

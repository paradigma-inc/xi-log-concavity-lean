import ProofWorkspace.Final.SourcePanel33BoundsFull
import ProofWorkspace.Final.SourcePanel33ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel33Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨33, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel33Candidate := by
  have hlast : (sourcePanel33Checkpoint 54).2 = sourcePanel33Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨33, by decide⟩ sourcePanel33Seed
    sourcePanel33Checkpoint sourcePanel33Seed_checked sourcePanel33Checkpoint_zero
    sourcePanel33Chunks_checked).trans hlast

theorem sourcePanel33_stream_passes :
    sourcePanelCheck ⟨33, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨33, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨33, by decide⟩)
    sourcePanel33Candidate_stream).trans sourcePanel33Candidate_passes

end ReciprocalXi

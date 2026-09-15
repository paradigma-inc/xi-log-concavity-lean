import ProofWorkspace.Final.SourcePanel223BoundsFull
import ProofWorkspace.Final.SourcePanel223ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel223Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨223, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel223Candidate := by
  have hlast : (sourcePanel223Checkpoint 54).2 = sourcePanel223Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨223, by decide⟩ sourcePanel223Seed
    sourcePanel223Checkpoint sourcePanel223Seed_checked sourcePanel223Checkpoint_zero
    sourcePanel223Chunks_checked).trans hlast

theorem sourcePanel223_stream_passes :
    sourcePanelCheck ⟨223, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨223, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨223, by decide⟩)
    sourcePanel223Candidate_stream).trans sourcePanel223Candidate_passes

end ReciprocalXi

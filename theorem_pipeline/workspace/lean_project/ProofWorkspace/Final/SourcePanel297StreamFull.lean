import ProofWorkspace.Final.SourcePanel297BoundsFull
import ProofWorkspace.Final.SourcePanel297ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel297Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨297, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel297Candidate := by
  have hlast : (sourcePanel297Checkpoint 54).2 = sourcePanel297Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨297, by decide⟩ sourcePanel297Seed
    sourcePanel297Checkpoint sourcePanel297Seed_checked sourcePanel297Checkpoint_zero
    sourcePanel297Chunks_checked).trans hlast

theorem sourcePanel297_stream_passes :
    sourcePanelCheck ⟨297, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨297, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨297, by decide⟩)
    sourcePanel297Candidate_stream).trans sourcePanel297Candidate_passes

end ReciprocalXi

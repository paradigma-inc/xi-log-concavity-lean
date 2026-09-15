import ProofWorkspace.Final.SourcePanel261BoundsFull
import ProofWorkspace.Final.SourcePanel261ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel261Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨261, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel261Candidate := by
  have hlast : (sourcePanel261Checkpoint 54).2 = sourcePanel261Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨261, by decide⟩ sourcePanel261Seed
    sourcePanel261Checkpoint sourcePanel261Seed_checked sourcePanel261Checkpoint_zero
    sourcePanel261Chunks_checked).trans hlast

theorem sourcePanel261_stream_passes :
    sourcePanelCheck ⟨261, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨261, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨261, by decide⟩)
    sourcePanel261Candidate_stream).trans sourcePanel261Candidate_passes

end ReciprocalXi

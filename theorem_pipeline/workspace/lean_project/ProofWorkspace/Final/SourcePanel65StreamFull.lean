import ProofWorkspace.Final.SourcePanel65BoundsFull
import ProofWorkspace.Final.SourcePanel65ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel65Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨65, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel65Candidate := by
  have hlast : (sourcePanel65Checkpoint 54).2 = sourcePanel65Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨65, by decide⟩ sourcePanel65Seed
    sourcePanel65Checkpoint sourcePanel65Seed_checked sourcePanel65Checkpoint_zero
    sourcePanel65Chunks_checked).trans hlast

theorem sourcePanel65_stream_passes :
    sourcePanelCheck ⟨65, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨65, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨65, by decide⟩)
    sourcePanel65Candidate_stream).trans sourcePanel65Candidate_passes

end ReciprocalXi

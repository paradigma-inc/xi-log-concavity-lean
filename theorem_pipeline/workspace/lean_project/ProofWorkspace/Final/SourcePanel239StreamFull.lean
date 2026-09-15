import ProofWorkspace.Final.SourcePanel239BoundsFull
import ProofWorkspace.Final.SourcePanel239ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel239Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨239, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel239Candidate := by
  have hlast : (sourcePanel239Checkpoint 54).2 = sourcePanel239Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨239, by decide⟩ sourcePanel239Seed
    sourcePanel239Checkpoint sourcePanel239Seed_checked sourcePanel239Checkpoint_zero
    sourcePanel239Chunks_checked).trans hlast

theorem sourcePanel239_stream_passes :
    sourcePanelCheck ⟨239, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨239, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨239, by decide⟩)
    sourcePanel239Candidate_stream).trans sourcePanel239Candidate_passes

end ReciprocalXi

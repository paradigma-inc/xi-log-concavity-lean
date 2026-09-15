import ProofWorkspace.Final.SourcePanel43BoundsFull
import ProofWorkspace.Final.SourcePanel43ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel43Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨43, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel43Candidate := by
  have hlast : (sourcePanel43Checkpoint 54).2 = sourcePanel43Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨43, by decide⟩ sourcePanel43Seed
    sourcePanel43Checkpoint sourcePanel43Seed_checked sourcePanel43Checkpoint_zero
    sourcePanel43Chunks_checked).trans hlast

theorem sourcePanel43_stream_passes :
    sourcePanelCheck ⟨43, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨43, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨43, by decide⟩)
    sourcePanel43Candidate_stream).trans sourcePanel43Candidate_passes

end ReciprocalXi

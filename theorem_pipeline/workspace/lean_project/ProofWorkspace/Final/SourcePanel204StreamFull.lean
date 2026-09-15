import ProofWorkspace.Final.SourcePanel204BoundsFull
import ProofWorkspace.Final.SourcePanel204ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel204Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨204, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel204Candidate := by
  have hlast : (sourcePanel204Checkpoint 54).2 = sourcePanel204Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨204, by decide⟩ sourcePanel204Seed
    sourcePanel204Checkpoint sourcePanel204Seed_checked sourcePanel204Checkpoint_zero
    sourcePanel204Chunks_checked).trans hlast

theorem sourcePanel204_stream_passes :
    sourcePanelCheck ⟨204, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨204, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨204, by decide⟩)
    sourcePanel204Candidate_stream).trans sourcePanel204Candidate_passes

end ReciprocalXi

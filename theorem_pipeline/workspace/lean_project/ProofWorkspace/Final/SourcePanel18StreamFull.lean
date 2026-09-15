import ProofWorkspace.Final.SourcePanel18BoundsFull
import ProofWorkspace.Final.SourcePanel18ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel18Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨18, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel18Candidate := by
  have hlast : (sourcePanel18Checkpoint 54).2 = sourcePanel18Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨18, by decide⟩ sourcePanel18Seed
    sourcePanel18Checkpoint sourcePanel18Seed_checked sourcePanel18Checkpoint_zero
    sourcePanel18Chunks_checked).trans hlast

theorem sourcePanel18_stream_passes :
    sourcePanelCheck ⟨18, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨18, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨18, by decide⟩)
    sourcePanel18Candidate_stream).trans sourcePanel18Candidate_passes

end ReciprocalXi

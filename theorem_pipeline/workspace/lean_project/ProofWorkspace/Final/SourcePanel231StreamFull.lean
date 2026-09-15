import ProofWorkspace.Final.SourcePanel231BoundsFull
import ProofWorkspace.Final.SourcePanel231ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel231Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨231, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel231Candidate := by
  have hlast : (sourcePanel231Checkpoint 54).2 = sourcePanel231Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨231, by decide⟩ sourcePanel231Seed
    sourcePanel231Checkpoint sourcePanel231Seed_checked sourcePanel231Checkpoint_zero
    sourcePanel231Chunks_checked).trans hlast

theorem sourcePanel231_stream_passes :
    sourcePanelCheck ⟨231, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨231, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨231, by decide⟩)
    sourcePanel231Candidate_stream).trans sourcePanel231Candidate_passes

end ReciprocalXi

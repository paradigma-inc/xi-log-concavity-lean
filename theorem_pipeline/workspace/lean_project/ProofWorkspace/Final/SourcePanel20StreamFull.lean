import ProofWorkspace.Final.SourcePanel20BoundsFull
import ProofWorkspace.Final.SourcePanel20ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel20Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨20, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel20Candidate := by
  have hlast : (sourcePanel20Checkpoint 54).2 = sourcePanel20Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨20, by decide⟩ sourcePanel20Seed
    sourcePanel20Checkpoint sourcePanel20Seed_checked sourcePanel20Checkpoint_zero
    sourcePanel20Chunks_checked).trans hlast

theorem sourcePanel20_stream_passes :
    sourcePanelCheck ⟨20, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨20, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨20, by decide⟩)
    sourcePanel20Candidate_stream).trans sourcePanel20Candidate_passes

end ReciprocalXi

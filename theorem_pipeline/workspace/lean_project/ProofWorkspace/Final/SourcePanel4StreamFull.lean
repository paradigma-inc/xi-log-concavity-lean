import ProofWorkspace.Final.SourcePanel4BoundsFull
import ProofWorkspace.Final.SourcePanel4ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel4Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨4, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel4Candidate := by
  have hlast : (sourcePanel4Checkpoint 54).2 = sourcePanel4Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨4, by decide⟩ sourcePanel4Seed
    sourcePanel4Checkpoint sourcePanel4Seed_checked sourcePanel4Checkpoint_zero
    sourcePanel4Chunks_checked).trans hlast

theorem sourcePanel4_stream_passes :
    sourcePanelCheck ⟨4, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨4, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨4, by decide⟩)
    sourcePanel4Candidate_stream).trans sourcePanel4Candidate_passes

end ReciprocalXi

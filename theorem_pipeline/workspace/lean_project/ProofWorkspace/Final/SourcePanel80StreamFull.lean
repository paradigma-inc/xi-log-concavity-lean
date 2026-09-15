import ProofWorkspace.Final.SourcePanel80BoundsFull
import ProofWorkspace.Final.SourcePanel80ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel80Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨80, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel80Candidate := by
  have hlast : (sourcePanel80Checkpoint 54).2 = sourcePanel80Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨80, by decide⟩ sourcePanel80Seed
    sourcePanel80Checkpoint sourcePanel80Seed_checked sourcePanel80Checkpoint_zero
    sourcePanel80Chunks_checked).trans hlast

theorem sourcePanel80_stream_passes :
    sourcePanelCheck ⟨80, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨80, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨80, by decide⟩)
    sourcePanel80Candidate_stream).trans sourcePanel80Candidate_passes

end ReciprocalXi

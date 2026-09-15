import ProofWorkspace.Final.SourcePanel8BoundsFull
import ProofWorkspace.Final.SourcePanel8ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel8Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨8, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel8Candidate := by
  have hlast : (sourcePanel8Checkpoint 54).2 = sourcePanel8Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨8, by decide⟩ sourcePanel8Seed
    sourcePanel8Checkpoint sourcePanel8Seed_checked sourcePanel8Checkpoint_zero
    sourcePanel8Chunks_checked).trans hlast

theorem sourcePanel8_stream_passes :
    sourcePanelCheck ⟨8, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨8, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨8, by decide⟩)
    sourcePanel8Candidate_stream).trans sourcePanel8Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel263BoundsFull
import ProofWorkspace.Final.SourcePanel263ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel263Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨263, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel263Candidate := by
  have hlast : (sourcePanel263Checkpoint 54).2 = sourcePanel263Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨263, by decide⟩ sourcePanel263Seed
    sourcePanel263Checkpoint sourcePanel263Seed_checked sourcePanel263Checkpoint_zero
    sourcePanel263Chunks_checked).trans hlast

theorem sourcePanel263_stream_passes :
    sourcePanelCheck ⟨263, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨263, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨263, by decide⟩)
    sourcePanel263Candidate_stream).trans sourcePanel263Candidate_passes

end ReciprocalXi

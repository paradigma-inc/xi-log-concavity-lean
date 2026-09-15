import ProofWorkspace.Final.SourcePanel64BoundsFull
import ProofWorkspace.Final.SourcePanel64ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel64Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨64, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel64Candidate := by
  have hlast : (sourcePanel64Checkpoint 54).2 = sourcePanel64Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨64, by decide⟩ sourcePanel64Seed
    sourcePanel64Checkpoint sourcePanel64Seed_checked sourcePanel64Checkpoint_zero
    sourcePanel64Chunks_checked).trans hlast

theorem sourcePanel64_stream_passes :
    sourcePanelCheck ⟨64, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨64, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨64, by decide⟩)
    sourcePanel64Candidate_stream).trans sourcePanel64Candidate_passes

end ReciprocalXi

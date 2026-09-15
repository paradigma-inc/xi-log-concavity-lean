import ProofWorkspace.Final.SourcePanel60BoundsFull
import ProofWorkspace.Final.SourcePanel60ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel60Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨60, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel60Candidate := by
  have hlast : (sourcePanel60Checkpoint 54).2 = sourcePanel60Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨60, by decide⟩ sourcePanel60Seed
    sourcePanel60Checkpoint sourcePanel60Seed_checked sourcePanel60Checkpoint_zero
    sourcePanel60Chunks_checked).trans hlast

theorem sourcePanel60_stream_passes :
    sourcePanelCheck ⟨60, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨60, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨60, by decide⟩)
    sourcePanel60Candidate_stream).trans sourcePanel60Candidate_passes

end ReciprocalXi

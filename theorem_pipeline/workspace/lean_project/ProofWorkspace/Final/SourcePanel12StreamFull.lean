import ProofWorkspace.Final.SourcePanel12BoundsFull
import ProofWorkspace.Final.SourcePanel12ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel12Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨12, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel12Candidate := by
  have hlast : (sourcePanel12Checkpoint 54).2 = sourcePanel12Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨12, by decide⟩ sourcePanel12Seed
    sourcePanel12Checkpoint sourcePanel12Seed_checked sourcePanel12Checkpoint_zero
    sourcePanel12Chunks_checked).trans hlast

theorem sourcePanel12_stream_passes :
    sourcePanelCheck ⟨12, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨12, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨12, by decide⟩)
    sourcePanel12Candidate_stream).trans sourcePanel12Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel143BoundsFull
import ProofWorkspace.Final.SourcePanel143ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel143Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨143, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel143Candidate := by
  have hlast : (sourcePanel143Checkpoint 54).2 = sourcePanel143Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨143, by decide⟩ sourcePanel143Seed
    sourcePanel143Checkpoint sourcePanel143Seed_checked sourcePanel143Checkpoint_zero
    sourcePanel143Chunks_checked).trans hlast

theorem sourcePanel143_stream_passes :
    sourcePanelCheck ⟨143, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨143, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨143, by decide⟩)
    sourcePanel143Candidate_stream).trans sourcePanel143Candidate_passes

end ReciprocalXi

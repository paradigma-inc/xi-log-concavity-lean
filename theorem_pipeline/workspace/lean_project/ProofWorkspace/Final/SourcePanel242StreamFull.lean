import ProofWorkspace.Final.SourcePanel242BoundsFull
import ProofWorkspace.Final.SourcePanel242ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel242Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨242, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel242Candidate := by
  have hlast : (sourcePanel242Checkpoint 54).2 = sourcePanel242Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨242, by decide⟩ sourcePanel242Seed
    sourcePanel242Checkpoint sourcePanel242Seed_checked sourcePanel242Checkpoint_zero
    sourcePanel242Chunks_checked).trans hlast

theorem sourcePanel242_stream_passes :
    sourcePanelCheck ⟨242, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨242, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨242, by decide⟩)
    sourcePanel242Candidate_stream).trans sourcePanel242Candidate_passes

end ReciprocalXi

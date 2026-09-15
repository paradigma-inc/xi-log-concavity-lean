import ProofWorkspace.Final.SourcePanel215BoundsFull
import ProofWorkspace.Final.SourcePanel215ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel215Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨215, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel215Candidate := by
  have hlast : (sourcePanel215Checkpoint 54).2 = sourcePanel215Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨215, by decide⟩ sourcePanel215Seed
    sourcePanel215Checkpoint sourcePanel215Seed_checked sourcePanel215Checkpoint_zero
    sourcePanel215Chunks_checked).trans hlast

theorem sourcePanel215_stream_passes :
    sourcePanelCheck ⟨215, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨215, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨215, by decide⟩)
    sourcePanel215Candidate_stream).trans sourcePanel215Candidate_passes

end ReciprocalXi

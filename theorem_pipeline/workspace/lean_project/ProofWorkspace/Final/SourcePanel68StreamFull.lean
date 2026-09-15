import ProofWorkspace.Final.SourcePanel68BoundsFull
import ProofWorkspace.Final.SourcePanel68ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel68Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨68, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel68Candidate := by
  have hlast : (sourcePanel68Checkpoint 54).2 = sourcePanel68Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨68, by decide⟩ sourcePanel68Seed
    sourcePanel68Checkpoint sourcePanel68Seed_checked sourcePanel68Checkpoint_zero
    sourcePanel68Chunks_checked).trans hlast

theorem sourcePanel68_stream_passes :
    sourcePanelCheck ⟨68, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨68, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨68, by decide⟩)
    sourcePanel68Candidate_stream).trans sourcePanel68Candidate_passes

end ReciprocalXi

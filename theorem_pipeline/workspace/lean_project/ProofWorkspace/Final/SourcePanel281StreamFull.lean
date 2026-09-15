import ProofWorkspace.Final.SourcePanel281BoundsFull
import ProofWorkspace.Final.SourcePanel281ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel281Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨281, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel281Candidate := by
  have hlast : (sourcePanel281Checkpoint 54).2 = sourcePanel281Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨281, by decide⟩ sourcePanel281Seed
    sourcePanel281Checkpoint sourcePanel281Seed_checked sourcePanel281Checkpoint_zero
    sourcePanel281Chunks_checked).trans hlast

theorem sourcePanel281_stream_passes :
    sourcePanelCheck ⟨281, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨281, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨281, by decide⟩)
    sourcePanel281Candidate_stream).trans sourcePanel281Candidate_passes

end ReciprocalXi

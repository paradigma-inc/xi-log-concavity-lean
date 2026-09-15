import ProofWorkspace.Final.SourcePanel88BoundsFull
import ProofWorkspace.Final.SourcePanel88ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel88Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨88, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel88Candidate := by
  have hlast : (sourcePanel88Checkpoint 54).2 = sourcePanel88Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨88, by decide⟩ sourcePanel88Seed
    sourcePanel88Checkpoint sourcePanel88Seed_checked sourcePanel88Checkpoint_zero
    sourcePanel88Chunks_checked).trans hlast

theorem sourcePanel88_stream_passes :
    sourcePanelCheck ⟨88, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨88, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨88, by decide⟩)
    sourcePanel88Candidate_stream).trans sourcePanel88Candidate_passes

end ReciprocalXi

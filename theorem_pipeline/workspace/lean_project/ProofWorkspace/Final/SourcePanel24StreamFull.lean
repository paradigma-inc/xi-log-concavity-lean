import ProofWorkspace.Final.SourcePanel24BoundsFull
import ProofWorkspace.Final.SourcePanel24ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel24Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨24, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel24Candidate := by
  have hlast : (sourcePanel24Checkpoint 54).2 = sourcePanel24Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨24, by decide⟩ sourcePanel24Seed
    sourcePanel24Checkpoint sourcePanel24Seed_checked sourcePanel24Checkpoint_zero
    sourcePanel24Chunks_checked).trans hlast

theorem sourcePanel24_stream_passes :
    sourcePanelCheck ⟨24, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨24, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨24, by decide⟩)
    sourcePanel24Candidate_stream).trans sourcePanel24Candidate_passes

end ReciprocalXi

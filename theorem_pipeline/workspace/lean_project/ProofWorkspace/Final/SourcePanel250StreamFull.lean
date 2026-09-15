import ProofWorkspace.Final.SourcePanel250BoundsFull
import ProofWorkspace.Final.SourcePanel250ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel250Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨250, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel250Candidate := by
  have hlast : (sourcePanel250Checkpoint 54).2 = sourcePanel250Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨250, by decide⟩ sourcePanel250Seed
    sourcePanel250Checkpoint sourcePanel250Seed_checked sourcePanel250Checkpoint_zero
    sourcePanel250Chunks_checked).trans hlast

theorem sourcePanel250_stream_passes :
    sourcePanelCheck ⟨250, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨250, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨250, by decide⟩)
    sourcePanel250Candidate_stream).trans sourcePanel250Candidate_passes

end ReciprocalXi

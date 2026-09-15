import ProofWorkspace.Final.SourcePanel232BoundsFull
import ProofWorkspace.Final.SourcePanel232ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel232Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨232, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel232Candidate := by
  have hlast : (sourcePanel232Checkpoint 54).2 = sourcePanel232Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨232, by decide⟩ sourcePanel232Seed
    sourcePanel232Checkpoint sourcePanel232Seed_checked sourcePanel232Checkpoint_zero
    sourcePanel232Chunks_checked).trans hlast

theorem sourcePanel232_stream_passes :
    sourcePanelCheck ⟨232, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨232, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨232, by decide⟩)
    sourcePanel232Candidate_stream).trans sourcePanel232Candidate_passes

end ReciprocalXi

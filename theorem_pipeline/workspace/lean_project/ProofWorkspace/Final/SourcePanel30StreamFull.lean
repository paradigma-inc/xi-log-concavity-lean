import ProofWorkspace.Final.SourcePanel30BoundsFull
import ProofWorkspace.Final.SourcePanel30ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel30Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨30, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel30Candidate := by
  have hlast : (sourcePanel30Checkpoint 54).2 = sourcePanel30Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨30, by decide⟩ sourcePanel30Seed
    sourcePanel30Checkpoint sourcePanel30Seed_checked sourcePanel30Checkpoint_zero
    sourcePanel30Chunks_checked).trans hlast

theorem sourcePanel30_stream_passes :
    sourcePanelCheck ⟨30, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨30, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨30, by decide⟩)
    sourcePanel30Candidate_stream).trans sourcePanel30Candidate_passes

end ReciprocalXi

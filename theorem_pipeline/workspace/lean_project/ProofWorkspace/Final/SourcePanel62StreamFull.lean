import ProofWorkspace.Final.SourcePanel62BoundsFull
import ProofWorkspace.Final.SourcePanel62ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel62Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨62, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel62Candidate := by
  have hlast : (sourcePanel62Checkpoint 54).2 = sourcePanel62Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨62, by decide⟩ sourcePanel62Seed
    sourcePanel62Checkpoint sourcePanel62Seed_checked sourcePanel62Checkpoint_zero
    sourcePanel62Chunks_checked).trans hlast

theorem sourcePanel62_stream_passes :
    sourcePanelCheck ⟨62, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨62, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨62, by decide⟩)
    sourcePanel62Candidate_stream).trans sourcePanel62Candidate_passes

end ReciprocalXi

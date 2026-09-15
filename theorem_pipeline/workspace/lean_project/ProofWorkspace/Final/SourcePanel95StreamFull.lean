import ProofWorkspace.Final.SourcePanel95BoundsFull
import ProofWorkspace.Final.SourcePanel95ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel95Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨95, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel95Candidate := by
  have hlast : (sourcePanel95Checkpoint 54).2 = sourcePanel95Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨95, by decide⟩ sourcePanel95Seed
    sourcePanel95Checkpoint sourcePanel95Seed_checked sourcePanel95Checkpoint_zero
    sourcePanel95Chunks_checked).trans hlast

theorem sourcePanel95_stream_passes :
    sourcePanelCheck ⟨95, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨95, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨95, by decide⟩)
    sourcePanel95Candidate_stream).trans sourcePanel95Candidate_passes

end ReciprocalXi

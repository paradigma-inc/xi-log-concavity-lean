import ProofWorkspace.Final.SourcePanel132BoundsFull
import ProofWorkspace.Final.SourcePanel132ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel132Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨132, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel132Candidate := by
  have hlast : (sourcePanel132Checkpoint 54).2 = sourcePanel132Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨132, by decide⟩ sourcePanel132Seed
    sourcePanel132Checkpoint sourcePanel132Seed_checked sourcePanel132Checkpoint_zero
    sourcePanel132Chunks_checked).trans hlast

theorem sourcePanel132_stream_passes :
    sourcePanelCheck ⟨132, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨132, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨132, by decide⟩)
    sourcePanel132Candidate_stream).trans sourcePanel132Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel257BoundsFull
import ProofWorkspace.Final.SourcePanel257ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel257Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨257, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel257Candidate := by
  have hlast : (sourcePanel257Checkpoint 54).2 = sourcePanel257Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨257, by decide⟩ sourcePanel257Seed
    sourcePanel257Checkpoint sourcePanel257Seed_checked sourcePanel257Checkpoint_zero
    sourcePanel257Chunks_checked).trans hlast

theorem sourcePanel257_stream_passes :
    sourcePanelCheck ⟨257, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨257, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨257, by decide⟩)
    sourcePanel257Candidate_stream).trans sourcePanel257Candidate_passes

end ReciprocalXi

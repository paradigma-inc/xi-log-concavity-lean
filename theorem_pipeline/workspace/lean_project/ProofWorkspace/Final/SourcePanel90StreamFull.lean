import ProofWorkspace.Final.SourcePanel90BoundsFull
import ProofWorkspace.Final.SourcePanel90ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel90Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨90, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel90Candidate := by
  have hlast : (sourcePanel90Checkpoint 54).2 = sourcePanel90Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨90, by decide⟩ sourcePanel90Seed
    sourcePanel90Checkpoint sourcePanel90Seed_checked sourcePanel90Checkpoint_zero
    sourcePanel90Chunks_checked).trans hlast

theorem sourcePanel90_stream_passes :
    sourcePanelCheck ⟨90, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨90, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨90, by decide⟩)
    sourcePanel90Candidate_stream).trans sourcePanel90Candidate_passes

end ReciprocalXi

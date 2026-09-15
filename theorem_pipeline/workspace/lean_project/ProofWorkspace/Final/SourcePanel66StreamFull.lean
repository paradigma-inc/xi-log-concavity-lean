import ProofWorkspace.Final.SourcePanel66BoundsFull
import ProofWorkspace.Final.SourcePanel66ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel66Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨66, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel66Candidate := by
  have hlast : (sourcePanel66Checkpoint 54).2 = sourcePanel66Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨66, by decide⟩ sourcePanel66Seed
    sourcePanel66Checkpoint sourcePanel66Seed_checked sourcePanel66Checkpoint_zero
    sourcePanel66Chunks_checked).trans hlast

theorem sourcePanel66_stream_passes :
    sourcePanelCheck ⟨66, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨66, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨66, by decide⟩)
    sourcePanel66Candidate_stream).trans sourcePanel66Candidate_passes

end ReciprocalXi

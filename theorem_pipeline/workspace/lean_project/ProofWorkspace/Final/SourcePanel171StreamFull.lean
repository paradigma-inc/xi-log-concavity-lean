import ProofWorkspace.Final.SourcePanel171BoundsFull
import ProofWorkspace.Final.SourcePanel171ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel171Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨171, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel171Candidate := by
  have hlast : (sourcePanel171Checkpoint 54).2 = sourcePanel171Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨171, by decide⟩ sourcePanel171Seed
    sourcePanel171Checkpoint sourcePanel171Seed_checked sourcePanel171Checkpoint_zero
    sourcePanel171Chunks_checked).trans hlast

theorem sourcePanel171_stream_passes :
    sourcePanelCheck ⟨171, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨171, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨171, by decide⟩)
    sourcePanel171Candidate_stream).trans sourcePanel171Candidate_passes

end ReciprocalXi

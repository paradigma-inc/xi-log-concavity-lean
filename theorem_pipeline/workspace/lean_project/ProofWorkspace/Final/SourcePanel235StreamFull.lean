import ProofWorkspace.Final.SourcePanel235BoundsFull
import ProofWorkspace.Final.SourcePanel235ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel235Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨235, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel235Candidate := by
  have hlast : (sourcePanel235Checkpoint 54).2 = sourcePanel235Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨235, by decide⟩ sourcePanel235Seed
    sourcePanel235Checkpoint sourcePanel235Seed_checked sourcePanel235Checkpoint_zero
    sourcePanel235Chunks_checked).trans hlast

theorem sourcePanel235_stream_passes :
    sourcePanelCheck ⟨235, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨235, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨235, by decide⟩)
    sourcePanel235Candidate_stream).trans sourcePanel235Candidate_passes

end ReciprocalXi

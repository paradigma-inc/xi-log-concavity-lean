import ProofWorkspace.Final.SourcePanel208BoundsFull
import ProofWorkspace.Final.SourcePanel208ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel208Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨208, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel208Candidate := by
  have hlast : (sourcePanel208Checkpoint 54).2 = sourcePanel208Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨208, by decide⟩ sourcePanel208Seed
    sourcePanel208Checkpoint sourcePanel208Seed_checked sourcePanel208Checkpoint_zero
    sourcePanel208Chunks_checked).trans hlast

theorem sourcePanel208_stream_passes :
    sourcePanelCheck ⟨208, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨208, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨208, by decide⟩)
    sourcePanel208Candidate_stream).trans sourcePanel208Candidate_passes

end ReciprocalXi

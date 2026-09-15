import ProofWorkspace.Final.SourcePanel130BoundsFull
import ProofWorkspace.Final.SourcePanel130ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel130Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨130, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel130Candidate := by
  have hlast : (sourcePanel130Checkpoint 54).2 = sourcePanel130Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨130, by decide⟩ sourcePanel130Seed
    sourcePanel130Checkpoint sourcePanel130Seed_checked sourcePanel130Checkpoint_zero
    sourcePanel130Chunks_checked).trans hlast

theorem sourcePanel130_stream_passes :
    sourcePanelCheck ⟨130, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨130, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨130, by decide⟩)
    sourcePanel130Candidate_stream).trans sourcePanel130Candidate_passes

end ReciprocalXi

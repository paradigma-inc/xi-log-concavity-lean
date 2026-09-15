import ProofWorkspace.Final.SourcePanel293BoundsFull
import ProofWorkspace.Final.SourcePanel293ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel293Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨293, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel293Candidate := by
  have hlast : (sourcePanel293Checkpoint 54).2 = sourcePanel293Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨293, by decide⟩ sourcePanel293Seed
    sourcePanel293Checkpoint sourcePanel293Seed_checked sourcePanel293Checkpoint_zero
    sourcePanel293Chunks_checked).trans hlast

theorem sourcePanel293_stream_passes :
    sourcePanelCheck ⟨293, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨293, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨293, by decide⟩)
    sourcePanel293Candidate_stream).trans sourcePanel293Candidate_passes

end ReciprocalXi

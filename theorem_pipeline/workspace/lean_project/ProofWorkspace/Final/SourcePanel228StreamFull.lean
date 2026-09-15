import ProofWorkspace.Final.SourcePanel228BoundsFull
import ProofWorkspace.Final.SourcePanel228ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel228Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨228, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel228Candidate := by
  have hlast : (sourcePanel228Checkpoint 54).2 = sourcePanel228Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨228, by decide⟩ sourcePanel228Seed
    sourcePanel228Checkpoint sourcePanel228Seed_checked sourcePanel228Checkpoint_zero
    sourcePanel228Chunks_checked).trans hlast

theorem sourcePanel228_stream_passes :
    sourcePanelCheck ⟨228, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨228, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨228, by decide⟩)
    sourcePanel228Candidate_stream).trans sourcePanel228Candidate_passes

end ReciprocalXi

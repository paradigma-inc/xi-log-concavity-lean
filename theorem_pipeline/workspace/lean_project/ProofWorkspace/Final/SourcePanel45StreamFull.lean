import ProofWorkspace.Final.SourcePanel45BoundsFull
import ProofWorkspace.Final.SourcePanel45ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel45Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨45, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel45Candidate := by
  have hlast : (sourcePanel45Checkpoint 54).2 = sourcePanel45Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨45, by decide⟩ sourcePanel45Seed
    sourcePanel45Checkpoint sourcePanel45Seed_checked sourcePanel45Checkpoint_zero
    sourcePanel45Chunks_checked).trans hlast

theorem sourcePanel45_stream_passes :
    sourcePanelCheck ⟨45, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨45, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨45, by decide⟩)
    sourcePanel45Candidate_stream).trans sourcePanel45Candidate_passes

end ReciprocalXi

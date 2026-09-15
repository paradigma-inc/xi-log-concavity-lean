import ProofWorkspace.Final.SourcePanel161BoundsFull
import ProofWorkspace.Final.SourcePanel161ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel161Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨161, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel161Candidate := by
  have hlast : (sourcePanel161Checkpoint 54).2 = sourcePanel161Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨161, by decide⟩ sourcePanel161Seed
    sourcePanel161Checkpoint sourcePanel161Seed_checked sourcePanel161Checkpoint_zero
    sourcePanel161Chunks_checked).trans hlast

theorem sourcePanel161_stream_passes :
    sourcePanelCheck ⟨161, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨161, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨161, by decide⟩)
    sourcePanel161Candidate_stream).trans sourcePanel161Candidate_passes

end ReciprocalXi

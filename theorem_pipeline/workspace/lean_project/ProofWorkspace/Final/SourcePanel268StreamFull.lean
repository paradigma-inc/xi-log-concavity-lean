import ProofWorkspace.Final.SourcePanel268BoundsFull
import ProofWorkspace.Final.SourcePanel268ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel268Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨268, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel268Candidate := by
  have hlast : (sourcePanel268Checkpoint 54).2 = sourcePanel268Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨268, by decide⟩ sourcePanel268Seed
    sourcePanel268Checkpoint sourcePanel268Seed_checked sourcePanel268Checkpoint_zero
    sourcePanel268Chunks_checked).trans hlast

theorem sourcePanel268_stream_passes :
    sourcePanelCheck ⟨268, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨268, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨268, by decide⟩)
    sourcePanel268Candidate_stream).trans sourcePanel268Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel202BoundsFull
import ProofWorkspace.Final.SourcePanel202ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel202Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨202, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel202Candidate := by
  have hlast : (sourcePanel202Checkpoint 54).2 = sourcePanel202Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨202, by decide⟩ sourcePanel202Seed
    sourcePanel202Checkpoint sourcePanel202Seed_checked sourcePanel202Checkpoint_zero
    sourcePanel202Chunks_checked).trans hlast

theorem sourcePanel202_stream_passes :
    sourcePanelCheck ⟨202, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨202, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨202, by decide⟩)
    sourcePanel202Candidate_stream).trans sourcePanel202Candidate_passes

end ReciprocalXi

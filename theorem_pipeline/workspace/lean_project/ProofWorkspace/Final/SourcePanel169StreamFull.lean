import ProofWorkspace.Final.SourcePanel169BoundsFull
import ProofWorkspace.Final.SourcePanel169ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel169Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨169, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel169Candidate := by
  have hlast : (sourcePanel169Checkpoint 54).2 = sourcePanel169Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨169, by decide⟩ sourcePanel169Seed
    sourcePanel169Checkpoint sourcePanel169Seed_checked sourcePanel169Checkpoint_zero
    sourcePanel169Chunks_checked).trans hlast

theorem sourcePanel169_stream_passes :
    sourcePanelCheck ⟨169, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨169, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨169, by decide⟩)
    sourcePanel169Candidate_stream).trans sourcePanel169Candidate_passes

end ReciprocalXi

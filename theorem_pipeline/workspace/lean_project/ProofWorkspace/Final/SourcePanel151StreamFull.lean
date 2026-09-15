import ProofWorkspace.Final.SourcePanel151BoundsFull
import ProofWorkspace.Final.SourcePanel151ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel151Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨151, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel151Candidate := by
  have hlast : (sourcePanel151Checkpoint 54).2 = sourcePanel151Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨151, by decide⟩ sourcePanel151Seed
    sourcePanel151Checkpoint sourcePanel151Seed_checked sourcePanel151Checkpoint_zero
    sourcePanel151Chunks_checked).trans hlast

theorem sourcePanel151_stream_passes :
    sourcePanelCheck ⟨151, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨151, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨151, by decide⟩)
    sourcePanel151Candidate_stream).trans sourcePanel151Candidate_passes

end ReciprocalXi

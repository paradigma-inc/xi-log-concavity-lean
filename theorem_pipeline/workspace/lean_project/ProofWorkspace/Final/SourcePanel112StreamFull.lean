import ProofWorkspace.Final.SourcePanel112BoundsFull
import ProofWorkspace.Final.SourcePanel112ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel112Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨112, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel112Candidate := by
  have hlast : (sourcePanel112Checkpoint 54).2 = sourcePanel112Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨112, by decide⟩ sourcePanel112Seed
    sourcePanel112Checkpoint sourcePanel112Seed_checked sourcePanel112Checkpoint_zero
    sourcePanel112Chunks_checked).trans hlast

theorem sourcePanel112_stream_passes :
    sourcePanelCheck ⟨112, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨112, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨112, by decide⟩)
    sourcePanel112Candidate_stream).trans sourcePanel112Candidate_passes

end ReciprocalXi

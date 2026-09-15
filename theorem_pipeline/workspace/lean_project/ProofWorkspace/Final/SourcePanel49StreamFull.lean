import ProofWorkspace.Final.SourcePanel49BoundsFull
import ProofWorkspace.Final.SourcePanel49ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel49Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨49, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel49Candidate := by
  have hlast : (sourcePanel49Checkpoint 54).2 = sourcePanel49Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨49, by decide⟩ sourcePanel49Seed
    sourcePanel49Checkpoint sourcePanel49Seed_checked sourcePanel49Checkpoint_zero
    sourcePanel49Chunks_checked).trans hlast

theorem sourcePanel49_stream_passes :
    sourcePanelCheck ⟨49, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨49, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨49, by decide⟩)
    sourcePanel49Candidate_stream).trans sourcePanel49Candidate_passes

end ReciprocalXi

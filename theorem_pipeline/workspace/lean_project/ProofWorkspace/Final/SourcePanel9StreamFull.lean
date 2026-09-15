import ProofWorkspace.Final.SourcePanel9BoundsFull
import ProofWorkspace.Final.SourcePanel9ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel9Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨9, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel9Candidate := by
  have hlast : (sourcePanel9Checkpoint 54).2 = sourcePanel9Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨9, by decide⟩ sourcePanel9Seed
    sourcePanel9Checkpoint sourcePanel9Seed_checked sourcePanel9Checkpoint_zero
    sourcePanel9Chunks_checked).trans hlast

theorem sourcePanel9_stream_passes :
    sourcePanelCheck ⟨9, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨9, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨9, by decide⟩)
    sourcePanel9Candidate_stream).trans sourcePanel9Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel136BoundsFull
import ProofWorkspace.Final.SourcePanel136ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel136Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨136, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel136Candidate := by
  have hlast : (sourcePanel136Checkpoint 54).2 = sourcePanel136Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨136, by decide⟩ sourcePanel136Seed
    sourcePanel136Checkpoint sourcePanel136Seed_checked sourcePanel136Checkpoint_zero
    sourcePanel136Chunks_checked).trans hlast

theorem sourcePanel136_stream_passes :
    sourcePanelCheck ⟨136, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨136, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨136, by decide⟩)
    sourcePanel136Candidate_stream).trans sourcePanel136Candidate_passes

end ReciprocalXi

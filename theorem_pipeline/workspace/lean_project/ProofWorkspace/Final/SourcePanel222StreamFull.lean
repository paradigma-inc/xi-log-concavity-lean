import ProofWorkspace.Final.SourcePanel222BoundsFull
import ProofWorkspace.Final.SourcePanel222ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel222Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨222, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel222Candidate := by
  have hlast : (sourcePanel222Checkpoint 54).2 = sourcePanel222Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨222, by decide⟩ sourcePanel222Seed
    sourcePanel222Checkpoint sourcePanel222Seed_checked sourcePanel222Checkpoint_zero
    sourcePanel222Chunks_checked).trans hlast

theorem sourcePanel222_stream_passes :
    sourcePanelCheck ⟨222, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨222, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨222, by decide⟩)
    sourcePanel222Candidate_stream).trans sourcePanel222Candidate_passes

end ReciprocalXi

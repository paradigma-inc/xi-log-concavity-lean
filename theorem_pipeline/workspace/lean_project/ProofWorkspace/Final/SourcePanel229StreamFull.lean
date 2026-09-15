import ProofWorkspace.Final.SourcePanel229BoundsFull
import ProofWorkspace.Final.SourcePanel229ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel229Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨229, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel229Candidate := by
  have hlast : (sourcePanel229Checkpoint 54).2 = sourcePanel229Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨229, by decide⟩ sourcePanel229Seed
    sourcePanel229Checkpoint sourcePanel229Seed_checked sourcePanel229Checkpoint_zero
    sourcePanel229Chunks_checked).trans hlast

theorem sourcePanel229_stream_passes :
    sourcePanelCheck ⟨229, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨229, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨229, by decide⟩)
    sourcePanel229Candidate_stream).trans sourcePanel229Candidate_passes

end ReciprocalXi

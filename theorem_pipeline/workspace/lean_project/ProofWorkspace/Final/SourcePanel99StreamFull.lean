import ProofWorkspace.Final.SourcePanel99BoundsFull
import ProofWorkspace.Final.SourcePanel99ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel99Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨99, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel99Candidate := by
  have hlast : (sourcePanel99Checkpoint 54).2 = sourcePanel99Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨99, by decide⟩ sourcePanel99Seed
    sourcePanel99Checkpoint sourcePanel99Seed_checked sourcePanel99Checkpoint_zero
    sourcePanel99Chunks_checked).trans hlast

theorem sourcePanel99_stream_passes :
    sourcePanelCheck ⟨99, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨99, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨99, by decide⟩)
    sourcePanel99Candidate_stream).trans sourcePanel99Candidate_passes

end ReciprocalXi

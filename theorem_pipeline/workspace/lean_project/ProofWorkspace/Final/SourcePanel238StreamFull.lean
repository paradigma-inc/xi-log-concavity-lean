import ProofWorkspace.Final.SourcePanel238BoundsFull
import ProofWorkspace.Final.SourcePanel238ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel238Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨238, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel238Candidate := by
  have hlast : (sourcePanel238Checkpoint 54).2 = sourcePanel238Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨238, by decide⟩ sourcePanel238Seed
    sourcePanel238Checkpoint sourcePanel238Seed_checked sourcePanel238Checkpoint_zero
    sourcePanel238Chunks_checked).trans hlast

theorem sourcePanel238_stream_passes :
    sourcePanelCheck ⟨238, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨238, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨238, by decide⟩)
    sourcePanel238Candidate_stream).trans sourcePanel238Candidate_passes

end ReciprocalXi

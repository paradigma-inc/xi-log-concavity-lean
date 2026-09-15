import ProofWorkspace.Final.SourcePanel290BoundsFull
import ProofWorkspace.Final.SourcePanel290ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel290Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨290, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel290Candidate := by
  have hlast : (sourcePanel290Checkpoint 54).2 = sourcePanel290Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨290, by decide⟩ sourcePanel290Seed
    sourcePanel290Checkpoint sourcePanel290Seed_checked sourcePanel290Checkpoint_zero
    sourcePanel290Chunks_checked).trans hlast

theorem sourcePanel290_stream_passes :
    sourcePanelCheck ⟨290, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨290, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨290, by decide⟩)
    sourcePanel290Candidate_stream).trans sourcePanel290Candidate_passes

end ReciprocalXi

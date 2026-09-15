import ProofWorkspace.Final.SourcePanel307BoundsFull
import ProofWorkspace.Final.SourcePanel307ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel307Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨307, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel307Candidate := by
  have hlast : (sourcePanel307Checkpoint 54).2 = sourcePanel307Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨307, by decide⟩ sourcePanel307Seed
    sourcePanel307Checkpoint sourcePanel307Seed_checked sourcePanel307Checkpoint_zero
    sourcePanel307Chunks_checked).trans hlast

theorem sourcePanel307_stream_passes :
    sourcePanelCheck ⟨307, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨307, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨307, by decide⟩)
    sourcePanel307Candidate_stream).trans sourcePanel307Candidate_passes

end ReciprocalXi

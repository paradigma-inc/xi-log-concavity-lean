import ProofWorkspace.Final.SourcePanel154BoundsFull
import ProofWorkspace.Final.SourcePanel154ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel154Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨154, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel154Candidate := by
  have hlast : (sourcePanel154Checkpoint 54).2 = sourcePanel154Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨154, by decide⟩ sourcePanel154Seed
    sourcePanel154Checkpoint sourcePanel154Seed_checked sourcePanel154Checkpoint_zero
    sourcePanel154Chunks_checked).trans hlast

theorem sourcePanel154_stream_passes :
    sourcePanelCheck ⟨154, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨154, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨154, by decide⟩)
    sourcePanel154Candidate_stream).trans sourcePanel154Candidate_passes

end ReciprocalXi

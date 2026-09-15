import ProofWorkspace.Final.SourcePanel295BoundsFull
import ProofWorkspace.Final.SourcePanel295ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel295Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨295, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel295Candidate := by
  have hlast : (sourcePanel295Checkpoint 54).2 = sourcePanel295Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨295, by decide⟩ sourcePanel295Seed
    sourcePanel295Checkpoint sourcePanel295Seed_checked sourcePanel295Checkpoint_zero
    sourcePanel295Chunks_checked).trans hlast

theorem sourcePanel295_stream_passes :
    sourcePanelCheck ⟨295, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨295, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨295, by decide⟩)
    sourcePanel295Candidate_stream).trans sourcePanel295Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel247BoundsFull
import ProofWorkspace.Final.SourcePanel247ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel247Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨247, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel247Candidate := by
  have hlast : (sourcePanel247Checkpoint 54).2 = sourcePanel247Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨247, by decide⟩ sourcePanel247Seed
    sourcePanel247Checkpoint sourcePanel247Seed_checked sourcePanel247Checkpoint_zero
    sourcePanel247Chunks_checked).trans hlast

theorem sourcePanel247_stream_passes :
    sourcePanelCheck ⟨247, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨247, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨247, by decide⟩)
    sourcePanel247Candidate_stream).trans sourcePanel247Candidate_passes

end ReciprocalXi

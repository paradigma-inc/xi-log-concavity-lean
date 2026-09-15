import ProofWorkspace.Final.SourcePanel101BoundsFull
import ProofWorkspace.Final.SourcePanel101ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel101Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨101, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel101Candidate := by
  have hlast : (sourcePanel101Checkpoint 54).2 = sourcePanel101Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨101, by decide⟩ sourcePanel101Seed
    sourcePanel101Checkpoint sourcePanel101Seed_checked sourcePanel101Checkpoint_zero
    sourcePanel101Chunks_checked).trans hlast

theorem sourcePanel101_stream_passes :
    sourcePanelCheck ⟨101, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨101, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨101, by decide⟩)
    sourcePanel101Candidate_stream).trans sourcePanel101Candidate_passes

end ReciprocalXi

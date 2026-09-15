import ProofWorkspace.Final.SourcePanel292BoundsFull
import ProofWorkspace.Final.SourcePanel292ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel292Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨292, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel292Candidate := by
  have hlast : (sourcePanel292Checkpoint 54).2 = sourcePanel292Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨292, by decide⟩ sourcePanel292Seed
    sourcePanel292Checkpoint sourcePanel292Seed_checked sourcePanel292Checkpoint_zero
    sourcePanel292Chunks_checked).trans hlast

theorem sourcePanel292_stream_passes :
    sourcePanelCheck ⟨292, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨292, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨292, by decide⟩)
    sourcePanel292Candidate_stream).trans sourcePanel292Candidate_passes

end ReciprocalXi

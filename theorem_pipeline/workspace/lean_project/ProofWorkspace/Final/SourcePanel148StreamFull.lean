import ProofWorkspace.Final.SourcePanel148BoundsFull
import ProofWorkspace.Final.SourcePanel148ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel148Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨148, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel148Candidate := by
  have hlast : (sourcePanel148Checkpoint 54).2 = sourcePanel148Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨148, by decide⟩ sourcePanel148Seed
    sourcePanel148Checkpoint sourcePanel148Seed_checked sourcePanel148Checkpoint_zero
    sourcePanel148Chunks_checked).trans hlast

theorem sourcePanel148_stream_passes :
    sourcePanelCheck ⟨148, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨148, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨148, by decide⟩)
    sourcePanel148Candidate_stream).trans sourcePanel148Candidate_passes

end ReciprocalXi

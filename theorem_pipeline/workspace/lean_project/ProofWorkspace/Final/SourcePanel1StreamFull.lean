import ProofWorkspace.Final.SourcePanel1BoundsFull
import ProofWorkspace.Final.SourcePanel1ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel1Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨1, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel1Candidate := by
  have hlast : (sourcePanel1Checkpoint 54).2 = sourcePanel1Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨1, by decide⟩ sourcePanel1Seed
    sourcePanel1Checkpoint sourcePanel1Seed_checked sourcePanel1Checkpoint_zero
    sourcePanel1Chunks_checked).trans hlast

theorem sourcePanel1_stream_passes :
    sourcePanelCheck ⟨1, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨1, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨1, by decide⟩)
    sourcePanel1Candidate_stream).trans sourcePanel1Candidate_passes

end ReciprocalXi

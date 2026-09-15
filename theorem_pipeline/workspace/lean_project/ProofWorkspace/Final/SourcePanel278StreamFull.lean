import ProofWorkspace.Final.SourcePanel278BoundsFull
import ProofWorkspace.Final.SourcePanel278ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel278Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨278, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel278Candidate := by
  have hlast : (sourcePanel278Checkpoint 54).2 = sourcePanel278Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨278, by decide⟩ sourcePanel278Seed
    sourcePanel278Checkpoint sourcePanel278Seed_checked sourcePanel278Checkpoint_zero
    sourcePanel278Chunks_checked).trans hlast

theorem sourcePanel278_stream_passes :
    sourcePanelCheck ⟨278, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨278, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨278, by decide⟩)
    sourcePanel278Candidate_stream).trans sourcePanel278Candidate_passes

end ReciprocalXi

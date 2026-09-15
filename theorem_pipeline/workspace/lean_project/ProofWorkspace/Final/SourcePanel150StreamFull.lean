import ProofWorkspace.Final.SourcePanel150BoundsFull
import ProofWorkspace.Final.SourcePanel150ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel150Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨150, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel150Candidate := by
  have hlast : (sourcePanel150Checkpoint 54).2 = sourcePanel150Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨150, by decide⟩ sourcePanel150Seed
    sourcePanel150Checkpoint sourcePanel150Seed_checked sourcePanel150Checkpoint_zero
    sourcePanel150Chunks_checked).trans hlast

theorem sourcePanel150_stream_passes :
    sourcePanelCheck ⟨150, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨150, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨150, by decide⟩)
    sourcePanel150Candidate_stream).trans sourcePanel150Candidate_passes

end ReciprocalXi

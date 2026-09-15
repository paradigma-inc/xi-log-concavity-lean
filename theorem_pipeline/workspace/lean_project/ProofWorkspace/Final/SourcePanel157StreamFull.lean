import ProofWorkspace.Final.SourcePanel157BoundsFull
import ProofWorkspace.Final.SourcePanel157ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel157Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨157, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel157Candidate := by
  have hlast : (sourcePanel157Checkpoint 54).2 = sourcePanel157Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨157, by decide⟩ sourcePanel157Seed
    sourcePanel157Checkpoint sourcePanel157Seed_checked sourcePanel157Checkpoint_zero
    sourcePanel157Chunks_checked).trans hlast

theorem sourcePanel157_stream_passes :
    sourcePanelCheck ⟨157, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨157, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨157, by decide⟩)
    sourcePanel157Candidate_stream).trans sourcePanel157Candidate_passes

end ReciprocalXi

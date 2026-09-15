import ProofWorkspace.Final.SourcePanel267BoundsFull
import ProofWorkspace.Final.SourcePanel267ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel267Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨267, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel267Candidate := by
  have hlast : (sourcePanel267Checkpoint 54).2 = sourcePanel267Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨267, by decide⟩ sourcePanel267Seed
    sourcePanel267Checkpoint sourcePanel267Seed_checked sourcePanel267Checkpoint_zero
    sourcePanel267Chunks_checked).trans hlast

theorem sourcePanel267_stream_passes :
    sourcePanelCheck ⟨267, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨267, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨267, by decide⟩)
    sourcePanel267Candidate_stream).trans sourcePanel267Candidate_passes

end ReciprocalXi

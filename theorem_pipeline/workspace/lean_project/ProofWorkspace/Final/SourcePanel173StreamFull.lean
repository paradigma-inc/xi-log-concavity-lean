import ProofWorkspace.Final.SourcePanel173BoundsFull
import ProofWorkspace.Final.SourcePanel173ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel173Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨173, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel173Candidate := by
  have hlast : (sourcePanel173Checkpoint 54).2 = sourcePanel173Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨173, by decide⟩ sourcePanel173Seed
    sourcePanel173Checkpoint sourcePanel173Seed_checked sourcePanel173Checkpoint_zero
    sourcePanel173Chunks_checked).trans hlast

theorem sourcePanel173_stream_passes :
    sourcePanelCheck ⟨173, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨173, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨173, by decide⟩)
    sourcePanel173Candidate_stream).trans sourcePanel173Candidate_passes

end ReciprocalXi

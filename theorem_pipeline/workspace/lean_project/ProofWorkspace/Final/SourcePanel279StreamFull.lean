import ProofWorkspace.Final.SourcePanel279BoundsFull
import ProofWorkspace.Final.SourcePanel279ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel279Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨279, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel279Candidate := by
  have hlast : (sourcePanel279Checkpoint 54).2 = sourcePanel279Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨279, by decide⟩ sourcePanel279Seed
    sourcePanel279Checkpoint sourcePanel279Seed_checked sourcePanel279Checkpoint_zero
    sourcePanel279Chunks_checked).trans hlast

theorem sourcePanel279_stream_passes :
    sourcePanelCheck ⟨279, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨279, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨279, by decide⟩)
    sourcePanel279Candidate_stream).trans sourcePanel279Candidate_passes

end ReciprocalXi

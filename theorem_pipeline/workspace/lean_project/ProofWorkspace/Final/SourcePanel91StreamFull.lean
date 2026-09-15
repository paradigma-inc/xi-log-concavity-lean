import ProofWorkspace.Final.SourcePanel91BoundsFull
import ProofWorkspace.Final.SourcePanel91ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel91Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨91, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel91Candidate := by
  have hlast : (sourcePanel91Checkpoint 54).2 = sourcePanel91Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨91, by decide⟩ sourcePanel91Seed
    sourcePanel91Checkpoint sourcePanel91Seed_checked sourcePanel91Checkpoint_zero
    sourcePanel91Chunks_checked).trans hlast

theorem sourcePanel91_stream_passes :
    sourcePanelCheck ⟨91, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨91, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨91, by decide⟩)
    sourcePanel91Candidate_stream).trans sourcePanel91Candidate_passes

end ReciprocalXi

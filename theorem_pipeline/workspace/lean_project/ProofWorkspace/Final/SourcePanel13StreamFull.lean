import ProofWorkspace.Final.SourcePanel13BoundsFull
import ProofWorkspace.Final.SourcePanel13ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel13Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨13, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel13Candidate := by
  have hlast : (sourcePanel13Checkpoint 54).2 = sourcePanel13Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨13, by decide⟩ sourcePanel13Seed
    sourcePanel13Checkpoint sourcePanel13Seed_checked sourcePanel13Checkpoint_zero
    sourcePanel13Chunks_checked).trans hlast

theorem sourcePanel13_stream_passes :
    sourcePanelCheck ⟨13, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨13, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨13, by decide⟩)
    sourcePanel13Candidate_stream).trans sourcePanel13Candidate_passes

end ReciprocalXi

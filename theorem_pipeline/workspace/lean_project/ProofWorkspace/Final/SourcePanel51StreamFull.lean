import ProofWorkspace.Final.SourcePanel51BoundsFull
import ProofWorkspace.Final.SourcePanel51ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel51Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨51, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel51Candidate := by
  have hlast : (sourcePanel51Checkpoint 54).2 = sourcePanel51Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨51, by decide⟩ sourcePanel51Seed
    sourcePanel51Checkpoint sourcePanel51Seed_checked sourcePanel51Checkpoint_zero
    sourcePanel51Chunks_checked).trans hlast

theorem sourcePanel51_stream_passes :
    sourcePanelCheck ⟨51, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨51, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨51, by decide⟩)
    sourcePanel51Candidate_stream).trans sourcePanel51Candidate_passes

end ReciprocalXi

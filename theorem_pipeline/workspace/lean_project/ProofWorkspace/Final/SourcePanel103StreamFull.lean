import ProofWorkspace.Final.SourcePanel103BoundsFull
import ProofWorkspace.Final.SourcePanel103ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel103Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨103, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel103Candidate := by
  have hlast : (sourcePanel103Checkpoint 54).2 = sourcePanel103Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨103, by decide⟩ sourcePanel103Seed
    sourcePanel103Checkpoint sourcePanel103Seed_checked sourcePanel103Checkpoint_zero
    sourcePanel103Chunks_checked).trans hlast

theorem sourcePanel103_stream_passes :
    sourcePanelCheck ⟨103, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨103, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨103, by decide⟩)
    sourcePanel103Candidate_stream).trans sourcePanel103Candidate_passes

end ReciprocalXi

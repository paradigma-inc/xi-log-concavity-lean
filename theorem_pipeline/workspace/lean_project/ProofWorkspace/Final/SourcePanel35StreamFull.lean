import ProofWorkspace.Final.SourcePanel35BoundsFull
import ProofWorkspace.Final.SourcePanel35ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel35Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨35, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel35Candidate := by
  have hlast : (sourcePanel35Checkpoint 54).2 = sourcePanel35Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨35, by decide⟩ sourcePanel35Seed
    sourcePanel35Checkpoint sourcePanel35Seed_checked sourcePanel35Checkpoint_zero
    sourcePanel35Chunks_checked).trans hlast

theorem sourcePanel35_stream_passes :
    sourcePanelCheck ⟨35, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨35, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨35, by decide⟩)
    sourcePanel35Candidate_stream).trans sourcePanel35Candidate_passes

end ReciprocalXi

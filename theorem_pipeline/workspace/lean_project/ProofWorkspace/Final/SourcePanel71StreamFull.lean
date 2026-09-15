import ProofWorkspace.Final.SourcePanel71BoundsFull
import ProofWorkspace.Final.SourcePanel71ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel71Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨71, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel71Candidate := by
  have hlast : (sourcePanel71Checkpoint 54).2 = sourcePanel71Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨71, by decide⟩ sourcePanel71Seed
    sourcePanel71Checkpoint sourcePanel71Seed_checked sourcePanel71Checkpoint_zero
    sourcePanel71Chunks_checked).trans hlast

theorem sourcePanel71_stream_passes :
    sourcePanelCheck ⟨71, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨71, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨71, by decide⟩)
    sourcePanel71Candidate_stream).trans sourcePanel71Candidate_passes

end ReciprocalXi

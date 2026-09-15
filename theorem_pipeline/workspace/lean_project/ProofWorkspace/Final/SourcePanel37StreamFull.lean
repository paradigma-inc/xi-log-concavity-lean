import ProofWorkspace.Final.SourcePanel37BoundsFull
import ProofWorkspace.Final.SourcePanel37ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel37Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨37, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel37Candidate := by
  have hlast : (sourcePanel37Checkpoint 54).2 = sourcePanel37Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨37, by decide⟩ sourcePanel37Seed
    sourcePanel37Checkpoint sourcePanel37Seed_checked sourcePanel37Checkpoint_zero
    sourcePanel37Chunks_checked).trans hlast

theorem sourcePanel37_stream_passes :
    sourcePanelCheck ⟨37, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨37, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨37, by decide⟩)
    sourcePanel37Candidate_stream).trans sourcePanel37Candidate_passes

end ReciprocalXi

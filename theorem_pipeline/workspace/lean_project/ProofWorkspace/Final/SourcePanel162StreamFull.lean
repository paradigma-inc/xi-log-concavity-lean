import ProofWorkspace.Final.SourcePanel162BoundsFull
import ProofWorkspace.Final.SourcePanel162ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel162Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨162, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel162Candidate := by
  have hlast : (sourcePanel162Checkpoint 54).2 = sourcePanel162Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨162, by decide⟩ sourcePanel162Seed
    sourcePanel162Checkpoint sourcePanel162Seed_checked sourcePanel162Checkpoint_zero
    sourcePanel162Chunks_checked).trans hlast

theorem sourcePanel162_stream_passes :
    sourcePanelCheck ⟨162, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨162, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨162, by decide⟩)
    sourcePanel162Candidate_stream).trans sourcePanel162Candidate_passes

end ReciprocalXi

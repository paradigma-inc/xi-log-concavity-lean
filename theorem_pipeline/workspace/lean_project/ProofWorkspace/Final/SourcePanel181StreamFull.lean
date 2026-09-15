import ProofWorkspace.Final.SourcePanel181BoundsFull
import ProofWorkspace.Final.SourcePanel181ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel181Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨181, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel181Candidate := by
  have hlast : (sourcePanel181Checkpoint 54).2 = sourcePanel181Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨181, by decide⟩ sourcePanel181Seed
    sourcePanel181Checkpoint sourcePanel181Seed_checked sourcePanel181Checkpoint_zero
    sourcePanel181Chunks_checked).trans hlast

theorem sourcePanel181_stream_passes :
    sourcePanelCheck ⟨181, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨181, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨181, by decide⟩)
    sourcePanel181Candidate_stream).trans sourcePanel181Candidate_passes

end ReciprocalXi

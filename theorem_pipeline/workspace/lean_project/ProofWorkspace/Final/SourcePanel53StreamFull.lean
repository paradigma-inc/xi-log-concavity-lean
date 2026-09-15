import ProofWorkspace.Final.SourcePanel53BoundsFull
import ProofWorkspace.Final.SourcePanel53ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel53Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨53, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel53Candidate := by
  have hlast : (sourcePanel53Checkpoint 54).2 = sourcePanel53Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨53, by decide⟩ sourcePanel53Seed
    sourcePanel53Checkpoint sourcePanel53Seed_checked sourcePanel53Checkpoint_zero
    sourcePanel53Chunks_checked).trans hlast

theorem sourcePanel53_stream_passes :
    sourcePanelCheck ⟨53, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨53, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨53, by decide⟩)
    sourcePanel53Candidate_stream).trans sourcePanel53Candidate_passes

end ReciprocalXi

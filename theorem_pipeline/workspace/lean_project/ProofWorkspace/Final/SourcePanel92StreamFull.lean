import ProofWorkspace.Final.SourcePanel92BoundsFull
import ProofWorkspace.Final.SourcePanel92ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel92Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨92, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel92Candidate := by
  have hlast : (sourcePanel92Checkpoint 54).2 = sourcePanel92Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨92, by decide⟩ sourcePanel92Seed
    sourcePanel92Checkpoint sourcePanel92Seed_checked sourcePanel92Checkpoint_zero
    sourcePanel92Chunks_checked).trans hlast

theorem sourcePanel92_stream_passes :
    sourcePanelCheck ⟨92, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨92, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨92, by decide⟩)
    sourcePanel92Candidate_stream).trans sourcePanel92Candidate_passes

end ReciprocalXi

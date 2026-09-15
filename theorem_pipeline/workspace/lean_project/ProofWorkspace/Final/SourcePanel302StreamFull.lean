import ProofWorkspace.Final.SourcePanel302BoundsFull
import ProofWorkspace.Final.SourcePanel302ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel302Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨302, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel302Candidate := by
  have hlast : (sourcePanel302Checkpoint 54).2 = sourcePanel302Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨302, by decide⟩ sourcePanel302Seed
    sourcePanel302Checkpoint sourcePanel302Seed_checked sourcePanel302Checkpoint_zero
    sourcePanel302Chunks_checked).trans hlast

theorem sourcePanel302_stream_passes :
    sourcePanelCheck ⟨302, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨302, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨302, by decide⟩)
    sourcePanel302Candidate_stream).trans sourcePanel302Candidate_passes

end ReciprocalXi

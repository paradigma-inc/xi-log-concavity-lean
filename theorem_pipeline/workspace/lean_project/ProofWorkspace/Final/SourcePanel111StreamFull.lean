import ProofWorkspace.Final.SourcePanel111BoundsFull
import ProofWorkspace.Final.SourcePanel111ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel111Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨111, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel111Candidate := by
  have hlast : (sourcePanel111Checkpoint 54).2 = sourcePanel111Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨111, by decide⟩ sourcePanel111Seed
    sourcePanel111Checkpoint sourcePanel111Seed_checked sourcePanel111Checkpoint_zero
    sourcePanel111Chunks_checked).trans hlast

theorem sourcePanel111_stream_passes :
    sourcePanelCheck ⟨111, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨111, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨111, by decide⟩)
    sourcePanel111Candidate_stream).trans sourcePanel111Candidate_passes

end ReciprocalXi

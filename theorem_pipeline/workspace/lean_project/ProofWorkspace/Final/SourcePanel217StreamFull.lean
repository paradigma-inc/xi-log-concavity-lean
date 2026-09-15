import ProofWorkspace.Final.SourcePanel217BoundsFull
import ProofWorkspace.Final.SourcePanel217ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel217Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨217, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel217Candidate := by
  have hlast : (sourcePanel217Checkpoint 54).2 = sourcePanel217Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨217, by decide⟩ sourcePanel217Seed
    sourcePanel217Checkpoint sourcePanel217Seed_checked sourcePanel217Checkpoint_zero
    sourcePanel217Chunks_checked).trans hlast

theorem sourcePanel217_stream_passes :
    sourcePanelCheck ⟨217, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨217, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨217, by decide⟩)
    sourcePanel217Candidate_stream).trans sourcePanel217Candidate_passes

end ReciprocalXi

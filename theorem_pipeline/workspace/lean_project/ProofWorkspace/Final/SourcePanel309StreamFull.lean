import ProofWorkspace.Final.SourcePanel309BoundsFull
import ProofWorkspace.Final.SourcePanel309ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel309Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨309, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel309Candidate := by
  have hlast : (sourcePanel309Checkpoint 54).2 = sourcePanel309Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨309, by decide⟩ sourcePanel309Seed
    sourcePanel309Checkpoint sourcePanel309Seed_checked sourcePanel309Checkpoint_zero
    sourcePanel309Chunks_checked).trans hlast

theorem sourcePanel309_stream_passes :
    sourcePanelCheck ⟨309, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨309, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨309, by decide⟩)
    sourcePanel309Candidate_stream).trans sourcePanel309Candidate_passes

end ReciprocalXi

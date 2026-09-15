import ProofWorkspace.Final.SourcePanel140BoundsFull
import ProofWorkspace.Final.SourcePanel140ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel140Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨140, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel140Candidate := by
  have hlast : (sourcePanel140Checkpoint 54).2 = sourcePanel140Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨140, by decide⟩ sourcePanel140Seed
    sourcePanel140Checkpoint sourcePanel140Seed_checked sourcePanel140Checkpoint_zero
    sourcePanel140Chunks_checked).trans hlast

theorem sourcePanel140_stream_passes :
    sourcePanelCheck ⟨140, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨140, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨140, by decide⟩)
    sourcePanel140Candidate_stream).trans sourcePanel140Candidate_passes

end ReciprocalXi

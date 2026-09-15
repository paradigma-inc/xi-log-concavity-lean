import ProofWorkspace.Final.SourcePanel119BoundsFull
import ProofWorkspace.Final.SourcePanel119ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel119Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨119, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel119Candidate := by
  have hlast : (sourcePanel119Checkpoint 54).2 = sourcePanel119Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨119, by decide⟩ sourcePanel119Seed
    sourcePanel119Checkpoint sourcePanel119Seed_checked sourcePanel119Checkpoint_zero
    sourcePanel119Chunks_checked).trans hlast

theorem sourcePanel119_stream_passes :
    sourcePanelCheck ⟨119, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨119, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨119, by decide⟩)
    sourcePanel119Candidate_stream).trans sourcePanel119Candidate_passes

end ReciprocalXi

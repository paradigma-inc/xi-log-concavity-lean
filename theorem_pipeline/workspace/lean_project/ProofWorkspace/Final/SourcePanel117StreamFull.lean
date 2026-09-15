import ProofWorkspace.Final.SourcePanel117BoundsFull
import ProofWorkspace.Final.SourcePanel117ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel117Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨117, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel117Candidate := by
  have hlast : (sourcePanel117Checkpoint 54).2 = sourcePanel117Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨117, by decide⟩ sourcePanel117Seed
    sourcePanel117Checkpoint sourcePanel117Seed_checked sourcePanel117Checkpoint_zero
    sourcePanel117Chunks_checked).trans hlast

theorem sourcePanel117_stream_passes :
    sourcePanelCheck ⟨117, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨117, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨117, by decide⟩)
    sourcePanel117Candidate_stream).trans sourcePanel117Candidate_passes

end ReciprocalXi

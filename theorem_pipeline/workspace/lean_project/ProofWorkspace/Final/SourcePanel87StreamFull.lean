import ProofWorkspace.Final.SourcePanel87BoundsFull
import ProofWorkspace.Final.SourcePanel87ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel87Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨87, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel87Candidate := by
  have hlast : (sourcePanel87Checkpoint 54).2 = sourcePanel87Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨87, by decide⟩ sourcePanel87Seed
    sourcePanel87Checkpoint sourcePanel87Seed_checked sourcePanel87Checkpoint_zero
    sourcePanel87Chunks_checked).trans hlast

theorem sourcePanel87_stream_passes :
    sourcePanelCheck ⟨87, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨87, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨87, by decide⟩)
    sourcePanel87Candidate_stream).trans sourcePanel87Candidate_passes

end ReciprocalXi

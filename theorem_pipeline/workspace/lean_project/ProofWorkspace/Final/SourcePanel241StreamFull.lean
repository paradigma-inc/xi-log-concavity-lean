import ProofWorkspace.Final.SourcePanel241BoundsFull
import ProofWorkspace.Final.SourcePanel241ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel241Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨241, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel241Candidate := by
  have hlast : (sourcePanel241Checkpoint 54).2 = sourcePanel241Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨241, by decide⟩ sourcePanel241Seed
    sourcePanel241Checkpoint sourcePanel241Seed_checked sourcePanel241Checkpoint_zero
    sourcePanel241Chunks_checked).trans hlast

theorem sourcePanel241_stream_passes :
    sourcePanelCheck ⟨241, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨241, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨241, by decide⟩)
    sourcePanel241Candidate_stream).trans sourcePanel241Candidate_passes

end ReciprocalXi

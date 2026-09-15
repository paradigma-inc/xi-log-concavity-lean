import ProofWorkspace.Final.SourcePanel168BoundsFull
import ProofWorkspace.Final.SourcePanel168ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel168Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨168, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel168Candidate := by
  have hlast : (sourcePanel168Checkpoint 54).2 = sourcePanel168Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨168, by decide⟩ sourcePanel168Seed
    sourcePanel168Checkpoint sourcePanel168Seed_checked sourcePanel168Checkpoint_zero
    sourcePanel168Chunks_checked).trans hlast

theorem sourcePanel168_stream_passes :
    sourcePanelCheck ⟨168, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨168, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨168, by decide⟩)
    sourcePanel168Candidate_stream).trans sourcePanel168Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel276BoundsFull
import ProofWorkspace.Final.SourcePanel276ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel276Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨276, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel276Candidate := by
  have hlast : (sourcePanel276Checkpoint 54).2 = sourcePanel276Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨276, by decide⟩ sourcePanel276Seed
    sourcePanel276Checkpoint sourcePanel276Seed_checked sourcePanel276Checkpoint_zero
    sourcePanel276Chunks_checked).trans hlast

theorem sourcePanel276_stream_passes :
    sourcePanelCheck ⟨276, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨276, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨276, by decide⟩)
    sourcePanel276Candidate_stream).trans sourcePanel276Candidate_passes

end ReciprocalXi

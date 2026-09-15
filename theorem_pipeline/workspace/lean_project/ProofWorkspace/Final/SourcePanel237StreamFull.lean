import ProofWorkspace.Final.SourcePanel237BoundsFull
import ProofWorkspace.Final.SourcePanel237ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel237Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨237, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel237Candidate := by
  have hlast : (sourcePanel237Checkpoint 54).2 = sourcePanel237Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨237, by decide⟩ sourcePanel237Seed
    sourcePanel237Checkpoint sourcePanel237Seed_checked sourcePanel237Checkpoint_zero
    sourcePanel237Chunks_checked).trans hlast

theorem sourcePanel237_stream_passes :
    sourcePanelCheck ⟨237, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨237, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨237, by decide⟩)
    sourcePanel237Candidate_stream).trans sourcePanel237Candidate_passes

end ReciprocalXi

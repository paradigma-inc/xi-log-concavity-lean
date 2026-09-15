import ProofWorkspace.Final.SourcePanel224BoundsFull
import ProofWorkspace.Final.SourcePanel224ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel224Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨224, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel224Candidate := by
  have hlast : (sourcePanel224Checkpoint 54).2 = sourcePanel224Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨224, by decide⟩ sourcePanel224Seed
    sourcePanel224Checkpoint sourcePanel224Seed_checked sourcePanel224Checkpoint_zero
    sourcePanel224Chunks_checked).trans hlast

theorem sourcePanel224_stream_passes :
    sourcePanelCheck ⟨224, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨224, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨224, by decide⟩)
    sourcePanel224Candidate_stream).trans sourcePanel224Candidate_passes

end ReciprocalXi

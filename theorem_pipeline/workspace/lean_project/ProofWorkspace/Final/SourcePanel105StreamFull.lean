import ProofWorkspace.Final.SourcePanel105BoundsFull
import ProofWorkspace.Final.SourcePanel105ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel105Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨105, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel105Candidate := by
  have hlast : (sourcePanel105Checkpoint 54).2 = sourcePanel105Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨105, by decide⟩ sourcePanel105Seed
    sourcePanel105Checkpoint sourcePanel105Seed_checked sourcePanel105Checkpoint_zero
    sourcePanel105Chunks_checked).trans hlast

theorem sourcePanel105_stream_passes :
    sourcePanelCheck ⟨105, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨105, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨105, by decide⟩)
    sourcePanel105Candidate_stream).trans sourcePanel105Candidate_passes

end ReciprocalXi

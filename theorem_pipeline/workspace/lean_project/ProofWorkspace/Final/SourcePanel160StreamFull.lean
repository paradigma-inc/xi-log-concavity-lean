import ProofWorkspace.Final.SourcePanel160BoundsFull
import ProofWorkspace.Final.SourcePanel160ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel160Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨160, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel160Candidate := by
  have hlast : (sourcePanel160Checkpoint 54).2 = sourcePanel160Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨160, by decide⟩ sourcePanel160Seed
    sourcePanel160Checkpoint sourcePanel160Seed_checked sourcePanel160Checkpoint_zero
    sourcePanel160Chunks_checked).trans hlast

theorem sourcePanel160_stream_passes :
    sourcePanelCheck ⟨160, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨160, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨160, by decide⟩)
    sourcePanel160Candidate_stream).trans sourcePanel160Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel288BoundsFull
import ProofWorkspace.Final.SourcePanel288ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel288Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨288, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel288Candidate := by
  have hlast : (sourcePanel288Checkpoint 54).2 = sourcePanel288Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨288, by decide⟩ sourcePanel288Seed
    sourcePanel288Checkpoint sourcePanel288Seed_checked sourcePanel288Checkpoint_zero
    sourcePanel288Chunks_checked).trans hlast

theorem sourcePanel288_stream_passes :
    sourcePanelCheck ⟨288, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨288, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨288, by decide⟩)
    sourcePanel288Candidate_stream).trans sourcePanel288Candidate_passes

end ReciprocalXi

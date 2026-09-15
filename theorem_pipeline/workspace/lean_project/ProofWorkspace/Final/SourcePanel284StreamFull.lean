import ProofWorkspace.Final.SourcePanel284BoundsFull
import ProofWorkspace.Final.SourcePanel284ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel284Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨284, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel284Candidate := by
  have hlast : (sourcePanel284Checkpoint 54).2 = sourcePanel284Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨284, by decide⟩ sourcePanel284Seed
    sourcePanel284Checkpoint sourcePanel284Seed_checked sourcePanel284Checkpoint_zero
    sourcePanel284Chunks_checked).trans hlast

theorem sourcePanel284_stream_passes :
    sourcePanelCheck ⟨284, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨284, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨284, by decide⟩)
    sourcePanel284Candidate_stream).trans sourcePanel284Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel306BoundsFull
import ProofWorkspace.Final.SourcePanel306ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel306Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨306, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel306Candidate := by
  have hlast : (sourcePanel306Checkpoint 54).2 = sourcePanel306Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨306, by decide⟩ sourcePanel306Seed
    sourcePanel306Checkpoint sourcePanel306Seed_checked sourcePanel306Checkpoint_zero
    sourcePanel306Chunks_checked).trans hlast

theorem sourcePanel306_stream_passes :
    sourcePanelCheck ⟨306, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨306, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨306, by decide⟩)
    sourcePanel306Candidate_stream).trans sourcePanel306Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel226BoundsFull
import ProofWorkspace.Final.SourcePanel226ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel226Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨226, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel226Candidate := by
  have hlast : (sourcePanel226Checkpoint 54).2 = sourcePanel226Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨226, by decide⟩ sourcePanel226Seed
    sourcePanel226Checkpoint sourcePanel226Seed_checked sourcePanel226Checkpoint_zero
    sourcePanel226Chunks_checked).trans hlast

theorem sourcePanel226_stream_passes :
    sourcePanelCheck ⟨226, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨226, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨226, by decide⟩)
    sourcePanel226Candidate_stream).trans sourcePanel226Candidate_passes

end ReciprocalXi

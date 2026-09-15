import ProofWorkspace.Final.SourcePanel83BoundsFull
import ProofWorkspace.Final.SourcePanel83ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel83Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨83, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel83Candidate := by
  have hlast : (sourcePanel83Checkpoint 54).2 = sourcePanel83Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨83, by decide⟩ sourcePanel83Seed
    sourcePanel83Checkpoint sourcePanel83Seed_checked sourcePanel83Checkpoint_zero
    sourcePanel83Chunks_checked).trans hlast

theorem sourcePanel83_stream_passes :
    sourcePanelCheck ⟨83, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨83, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨83, by decide⟩)
    sourcePanel83Candidate_stream).trans sourcePanel83Candidate_passes

end ReciprocalXi

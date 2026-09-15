import ProofWorkspace.Final.SourcePanel79BoundsFull
import ProofWorkspace.Final.SourcePanel79ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel79Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨79, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel79Candidate := by
  have hlast : (sourcePanel79Checkpoint 54).2 = sourcePanel79Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨79, by decide⟩ sourcePanel79Seed
    sourcePanel79Checkpoint sourcePanel79Seed_checked sourcePanel79Checkpoint_zero
    sourcePanel79Chunks_checked).trans hlast

theorem sourcePanel79_stream_passes :
    sourcePanelCheck ⟨79, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨79, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨79, by decide⟩)
    sourcePanel79Candidate_stream).trans sourcePanel79Candidate_passes

end ReciprocalXi

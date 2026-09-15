import ProofWorkspace.Final.SourcePanel186BoundsFull
import ProofWorkspace.Final.SourcePanel186ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel186Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨186, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel186Candidate := by
  have hlast : (sourcePanel186Checkpoint 54).2 = sourcePanel186Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨186, by decide⟩ sourcePanel186Seed
    sourcePanel186Checkpoint sourcePanel186Seed_checked sourcePanel186Checkpoint_zero
    sourcePanel186Chunks_checked).trans hlast

theorem sourcePanel186_stream_passes :
    sourcePanelCheck ⟨186, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨186, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨186, by decide⟩)
    sourcePanel186Candidate_stream).trans sourcePanel186Candidate_passes

end ReciprocalXi

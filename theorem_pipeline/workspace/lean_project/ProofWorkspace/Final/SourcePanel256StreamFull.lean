import ProofWorkspace.Final.SourcePanel256BoundsFull
import ProofWorkspace.Final.SourcePanel256ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel256Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨256, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel256Candidate := by
  have hlast : (sourcePanel256Checkpoint 54).2 = sourcePanel256Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨256, by decide⟩ sourcePanel256Seed
    sourcePanel256Checkpoint sourcePanel256Seed_checked sourcePanel256Checkpoint_zero
    sourcePanel256Chunks_checked).trans hlast

theorem sourcePanel256_stream_passes :
    sourcePanelCheck ⟨256, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨256, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨256, by decide⟩)
    sourcePanel256Candidate_stream).trans sourcePanel256Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel142BoundsFull
import ProofWorkspace.Final.SourcePanel142ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel142Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨142, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel142Candidate := by
  have hlast : (sourcePanel142Checkpoint 54).2 = sourcePanel142Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨142, by decide⟩ sourcePanel142Seed
    sourcePanel142Checkpoint sourcePanel142Seed_checked sourcePanel142Checkpoint_zero
    sourcePanel142Chunks_checked).trans hlast

theorem sourcePanel142_stream_passes :
    sourcePanelCheck ⟨142, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨142, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨142, by decide⟩)
    sourcePanel142Candidate_stream).trans sourcePanel142Candidate_passes

end ReciprocalXi

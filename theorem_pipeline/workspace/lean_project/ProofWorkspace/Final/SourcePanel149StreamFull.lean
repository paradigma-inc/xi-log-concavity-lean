import ProofWorkspace.Final.SourcePanel149BoundsFull
import ProofWorkspace.Final.SourcePanel149ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel149Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨149, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel149Candidate := by
  have hlast : (sourcePanel149Checkpoint 54).2 = sourcePanel149Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨149, by decide⟩ sourcePanel149Seed
    sourcePanel149Checkpoint sourcePanel149Seed_checked sourcePanel149Checkpoint_zero
    sourcePanel149Chunks_checked).trans hlast

theorem sourcePanel149_stream_passes :
    sourcePanelCheck ⟨149, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨149, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨149, by decide⟩)
    sourcePanel149Candidate_stream).trans sourcePanel149Candidate_passes

end ReciprocalXi

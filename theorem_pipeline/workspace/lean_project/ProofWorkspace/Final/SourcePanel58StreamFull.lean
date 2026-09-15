import ProofWorkspace.Final.SourcePanel58BoundsFull
import ProofWorkspace.Final.SourcePanel58ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel58Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨58, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel58Candidate := by
  have hlast : (sourcePanel58Checkpoint 54).2 = sourcePanel58Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨58, by decide⟩ sourcePanel58Seed
    sourcePanel58Checkpoint sourcePanel58Seed_checked sourcePanel58Checkpoint_zero
    sourcePanel58Chunks_checked).trans hlast

theorem sourcePanel58_stream_passes :
    sourcePanelCheck ⟨58, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨58, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨58, by decide⟩)
    sourcePanel58Candidate_stream).trans sourcePanel58Candidate_passes

end ReciprocalXi

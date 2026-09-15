import ProofWorkspace.Final.SourcePanel116BoundsFull
import ProofWorkspace.Final.SourcePanel116ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel116Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨116, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel116Candidate := by
  have hlast : (sourcePanel116Checkpoint 54).2 = sourcePanel116Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨116, by decide⟩ sourcePanel116Seed
    sourcePanel116Checkpoint sourcePanel116Seed_checked sourcePanel116Checkpoint_zero
    sourcePanel116Chunks_checked).trans hlast

theorem sourcePanel116_stream_passes :
    sourcePanelCheck ⟨116, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨116, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨116, by decide⟩)
    sourcePanel116Candidate_stream).trans sourcePanel116Candidate_passes

end ReciprocalXi

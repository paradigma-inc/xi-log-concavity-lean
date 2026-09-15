import ProofWorkspace.Final.SourcePanel270BoundsFull
import ProofWorkspace.Final.SourcePanel270ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel270Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨270, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel270Candidate := by
  have hlast : (sourcePanel270Checkpoint 54).2 = sourcePanel270Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨270, by decide⟩ sourcePanel270Seed
    sourcePanel270Checkpoint sourcePanel270Seed_checked sourcePanel270Checkpoint_zero
    sourcePanel270Chunks_checked).trans hlast

theorem sourcePanel270_stream_passes :
    sourcePanelCheck ⟨270, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨270, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨270, by decide⟩)
    sourcePanel270Candidate_stream).trans sourcePanel270Candidate_passes

end ReciprocalXi

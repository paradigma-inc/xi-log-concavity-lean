import ProofWorkspace.Final.SourcePanel63BoundsFull
import ProofWorkspace.Final.SourcePanel63ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel63Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨63, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel63Candidate := by
  have hlast : (sourcePanel63Checkpoint 54).2 = sourcePanel63Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨63, by decide⟩ sourcePanel63Seed
    sourcePanel63Checkpoint sourcePanel63Seed_checked sourcePanel63Checkpoint_zero
    sourcePanel63Chunks_checked).trans hlast

theorem sourcePanel63_stream_passes :
    sourcePanelCheck ⟨63, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨63, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨63, by decide⟩)
    sourcePanel63Candidate_stream).trans sourcePanel63Candidate_passes

end ReciprocalXi

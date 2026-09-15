import ProofWorkspace.Final.SourcePanel254BoundsFull
import ProofWorkspace.Final.SourcePanel254ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel254Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨254, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel254Candidate := by
  have hlast : (sourcePanel254Checkpoint 54).2 = sourcePanel254Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨254, by decide⟩ sourcePanel254Seed
    sourcePanel254Checkpoint sourcePanel254Seed_checked sourcePanel254Checkpoint_zero
    sourcePanel254Chunks_checked).trans hlast

theorem sourcePanel254_stream_passes :
    sourcePanelCheck ⟨254, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨254, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨254, by decide⟩)
    sourcePanel254Candidate_stream).trans sourcePanel254Candidate_passes

end ReciprocalXi

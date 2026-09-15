import ProofWorkspace.Final.SourcePanel275BoundsFull
import ProofWorkspace.Final.SourcePanel275ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel275Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨275, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel275Candidate := by
  have hlast : (sourcePanel275Checkpoint 54).2 = sourcePanel275Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨275, by decide⟩ sourcePanel275Seed
    sourcePanel275Checkpoint sourcePanel275Seed_checked sourcePanel275Checkpoint_zero
    sourcePanel275Chunks_checked).trans hlast

theorem sourcePanel275_stream_passes :
    sourcePanelCheck ⟨275, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨275, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨275, by decide⟩)
    sourcePanel275Candidate_stream).trans sourcePanel275Candidate_passes

end ReciprocalXi

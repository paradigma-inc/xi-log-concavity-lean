import ProofWorkspace.Final.SourcePanel69BoundsFull
import ProofWorkspace.Final.SourcePanel69ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel69Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨69, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel69Candidate := by
  have hlast : (sourcePanel69Checkpoint 54).2 = sourcePanel69Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨69, by decide⟩ sourcePanel69Seed
    sourcePanel69Checkpoint sourcePanel69Seed_checked sourcePanel69Checkpoint_zero
    sourcePanel69Chunks_checked).trans hlast

theorem sourcePanel69_stream_passes :
    sourcePanelCheck ⟨69, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨69, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨69, by decide⟩)
    sourcePanel69Candidate_stream).trans sourcePanel69Candidate_passes

end ReciprocalXi

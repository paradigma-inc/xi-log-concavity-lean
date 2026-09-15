import ProofWorkspace.Final.SourcePanel248BoundsFull
import ProofWorkspace.Final.SourcePanel248ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel248Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨248, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel248Candidate := by
  have hlast : (sourcePanel248Checkpoint 54).2 = sourcePanel248Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨248, by decide⟩ sourcePanel248Seed
    sourcePanel248Checkpoint sourcePanel248Seed_checked sourcePanel248Checkpoint_zero
    sourcePanel248Chunks_checked).trans hlast

theorem sourcePanel248_stream_passes :
    sourcePanelCheck ⟨248, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨248, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨248, by decide⟩)
    sourcePanel248Candidate_stream).trans sourcePanel248Candidate_passes

end ReciprocalXi

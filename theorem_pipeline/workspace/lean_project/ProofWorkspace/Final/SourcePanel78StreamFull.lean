import ProofWorkspace.Final.SourcePanel78BoundsFull
import ProofWorkspace.Final.SourcePanel78ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel78Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨78, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel78Candidate := by
  have hlast : (sourcePanel78Checkpoint 54).2 = sourcePanel78Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨78, by decide⟩ sourcePanel78Seed
    sourcePanel78Checkpoint sourcePanel78Seed_checked sourcePanel78Checkpoint_zero
    sourcePanel78Chunks_checked).trans hlast

theorem sourcePanel78_stream_passes :
    sourcePanelCheck ⟨78, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨78, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨78, by decide⟩)
    sourcePanel78Candidate_stream).trans sourcePanel78Candidate_passes

end ReciprocalXi

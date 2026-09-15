import ProofWorkspace.Final.SourcePanel246BoundsFull
import ProofWorkspace.Final.SourcePanel246ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel246Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨246, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel246Candidate := by
  have hlast : (sourcePanel246Checkpoint 54).2 = sourcePanel246Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨246, by decide⟩ sourcePanel246Seed
    sourcePanel246Checkpoint sourcePanel246Seed_checked sourcePanel246Checkpoint_zero
    sourcePanel246Chunks_checked).trans hlast

theorem sourcePanel246_stream_passes :
    sourcePanelCheck ⟨246, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨246, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨246, by decide⟩)
    sourcePanel246Candidate_stream).trans sourcePanel246Candidate_passes

end ReciprocalXi

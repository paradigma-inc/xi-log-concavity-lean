import ProofWorkspace.Final.SourcePanel81BoundsFull
import ProofWorkspace.Final.SourcePanel81ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel81Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨81, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel81Candidate := by
  have hlast : (sourcePanel81Checkpoint 54).2 = sourcePanel81Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨81, by decide⟩ sourcePanel81Seed
    sourcePanel81Checkpoint sourcePanel81Seed_checked sourcePanel81Checkpoint_zero
    sourcePanel81Chunks_checked).trans hlast

theorem sourcePanel81_stream_passes :
    sourcePanelCheck ⟨81, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨81, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨81, by decide⟩)
    sourcePanel81Candidate_stream).trans sourcePanel81Candidate_passes

end ReciprocalXi

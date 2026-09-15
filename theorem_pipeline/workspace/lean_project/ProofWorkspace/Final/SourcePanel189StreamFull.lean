import ProofWorkspace.Final.SourcePanel189BoundsFull
import ProofWorkspace.Final.SourcePanel189ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel189Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨189, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel189Candidate := by
  have hlast : (sourcePanel189Checkpoint 54).2 = sourcePanel189Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨189, by decide⟩ sourcePanel189Seed
    sourcePanel189Checkpoint sourcePanel189Seed_checked sourcePanel189Checkpoint_zero
    sourcePanel189Chunks_checked).trans hlast

theorem sourcePanel189_stream_passes :
    sourcePanelCheck ⟨189, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨189, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨189, by decide⟩)
    sourcePanel189Candidate_stream).trans sourcePanel189Candidate_passes

end ReciprocalXi

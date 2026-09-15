import ProofWorkspace.Final.SourcePanel97BoundsFull
import ProofWorkspace.Final.SourcePanel97ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel97Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨97, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel97Candidate := by
  have hlast : (sourcePanel97Checkpoint 54).2 = sourcePanel97Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨97, by decide⟩ sourcePanel97Seed
    sourcePanel97Checkpoint sourcePanel97Seed_checked sourcePanel97Checkpoint_zero
    sourcePanel97Chunks_checked).trans hlast

theorem sourcePanel97_stream_passes :
    sourcePanelCheck ⟨97, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨97, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨97, by decide⟩)
    sourcePanel97Candidate_stream).trans sourcePanel97Candidate_passes

end ReciprocalXi

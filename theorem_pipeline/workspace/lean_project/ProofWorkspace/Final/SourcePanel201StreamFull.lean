import ProofWorkspace.Final.SourcePanel201BoundsFull
import ProofWorkspace.Final.SourcePanel201ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel201Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨201, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel201Candidate := by
  have hlast : (sourcePanel201Checkpoint 54).2 = sourcePanel201Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨201, by decide⟩ sourcePanel201Seed
    sourcePanel201Checkpoint sourcePanel201Seed_checked sourcePanel201Checkpoint_zero
    sourcePanel201Chunks_checked).trans hlast

theorem sourcePanel201_stream_passes :
    sourcePanelCheck ⟨201, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨201, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨201, by decide⟩)
    sourcePanel201Candidate_stream).trans sourcePanel201Candidate_passes

end ReciprocalXi

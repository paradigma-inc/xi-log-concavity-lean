import ProofWorkspace.Final.SourcePanel73BoundsFull
import ProofWorkspace.Final.SourcePanel73ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel73Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨73, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel73Candidate := by
  have hlast : (sourcePanel73Checkpoint 54).2 = sourcePanel73Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨73, by decide⟩ sourcePanel73Seed
    sourcePanel73Checkpoint sourcePanel73Seed_checked sourcePanel73Checkpoint_zero
    sourcePanel73Chunks_checked).trans hlast

theorem sourcePanel73_stream_passes :
    sourcePanelCheck ⟨73, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨73, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨73, by decide⟩)
    sourcePanel73Candidate_stream).trans sourcePanel73Candidate_passes

end ReciprocalXi

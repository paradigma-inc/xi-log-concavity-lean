import ProofWorkspace.Final.SourcePanel113BoundsFull
import ProofWorkspace.Final.SourcePanel113ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel113Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨113, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel113Candidate := by
  have hlast : (sourcePanel113Checkpoint 54).2 = sourcePanel113Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨113, by decide⟩ sourcePanel113Seed
    sourcePanel113Checkpoint sourcePanel113Seed_checked sourcePanel113Checkpoint_zero
    sourcePanel113Chunks_checked).trans hlast

theorem sourcePanel113_stream_passes :
    sourcePanelCheck ⟨113, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨113, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨113, by decide⟩)
    sourcePanel113Candidate_stream).trans sourcePanel113Candidate_passes

end ReciprocalXi

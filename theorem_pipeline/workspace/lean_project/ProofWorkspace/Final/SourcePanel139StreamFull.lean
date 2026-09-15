import ProofWorkspace.Final.SourcePanel139BoundsFull
import ProofWorkspace.Final.SourcePanel139ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel139Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨139, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel139Candidate := by
  have hlast : (sourcePanel139Checkpoint 54).2 = sourcePanel139Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨139, by decide⟩ sourcePanel139Seed
    sourcePanel139Checkpoint sourcePanel139Seed_checked sourcePanel139Checkpoint_zero
    sourcePanel139Chunks_checked).trans hlast

theorem sourcePanel139_stream_passes :
    sourcePanelCheck ⟨139, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨139, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨139, by decide⟩)
    sourcePanel139Candidate_stream).trans sourcePanel139Candidate_passes

end ReciprocalXi

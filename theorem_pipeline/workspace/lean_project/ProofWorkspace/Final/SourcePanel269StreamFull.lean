import ProofWorkspace.Final.SourcePanel269BoundsFull
import ProofWorkspace.Final.SourcePanel269ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel269Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨269, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel269Candidate := by
  have hlast : (sourcePanel269Checkpoint 54).2 = sourcePanel269Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨269, by decide⟩ sourcePanel269Seed
    sourcePanel269Checkpoint sourcePanel269Seed_checked sourcePanel269Checkpoint_zero
    sourcePanel269Chunks_checked).trans hlast

theorem sourcePanel269_stream_passes :
    sourcePanelCheck ⟨269, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨269, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨269, by decide⟩)
    sourcePanel269Candidate_stream).trans sourcePanel269Candidate_passes

end ReciprocalXi

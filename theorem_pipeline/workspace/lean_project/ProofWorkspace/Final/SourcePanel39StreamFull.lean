import ProofWorkspace.Final.SourcePanel39BoundsFull
import ProofWorkspace.Final.SourcePanel39ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel39Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨39, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel39Candidate := by
  have hlast : (sourcePanel39Checkpoint 54).2 = sourcePanel39Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨39, by decide⟩ sourcePanel39Seed
    sourcePanel39Checkpoint sourcePanel39Seed_checked sourcePanel39Checkpoint_zero
    sourcePanel39Chunks_checked).trans hlast

theorem sourcePanel39_stream_passes :
    sourcePanelCheck ⟨39, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨39, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨39, by decide⟩)
    sourcePanel39Candidate_stream).trans sourcePanel39Candidate_passes

end ReciprocalXi

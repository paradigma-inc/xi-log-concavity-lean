import ProofWorkspace.Final.SourcePanel152BoundsFull
import ProofWorkspace.Final.SourcePanel152ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel152Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨152, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel152Candidate := by
  have hlast : (sourcePanel152Checkpoint 54).2 = sourcePanel152Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨152, by decide⟩ sourcePanel152Seed
    sourcePanel152Checkpoint sourcePanel152Seed_checked sourcePanel152Checkpoint_zero
    sourcePanel152Chunks_checked).trans hlast

theorem sourcePanel152_stream_passes :
    sourcePanelCheck ⟨152, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨152, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨152, by decide⟩)
    sourcePanel152Candidate_stream).trans sourcePanel152Candidate_passes

end ReciprocalXi

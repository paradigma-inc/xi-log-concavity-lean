import ProofWorkspace.Final.SourcePanel221BoundsFull
import ProofWorkspace.Final.SourcePanel221ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel221Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨221, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel221Candidate := by
  have hlast : (sourcePanel221Checkpoint 54).2 = sourcePanel221Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨221, by decide⟩ sourcePanel221Seed
    sourcePanel221Checkpoint sourcePanel221Seed_checked sourcePanel221Checkpoint_zero
    sourcePanel221Chunks_checked).trans hlast

theorem sourcePanel221_stream_passes :
    sourcePanelCheck ⟨221, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨221, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨221, by decide⟩)
    sourcePanel221Candidate_stream).trans sourcePanel221Candidate_passes

end ReciprocalXi

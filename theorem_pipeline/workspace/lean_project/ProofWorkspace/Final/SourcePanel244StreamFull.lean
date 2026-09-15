import ProofWorkspace.Final.SourcePanel244BoundsFull
import ProofWorkspace.Final.SourcePanel244ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel244Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨244, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel244Candidate := by
  have hlast : (sourcePanel244Checkpoint 54).2 = sourcePanel244Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨244, by decide⟩ sourcePanel244Seed
    sourcePanel244Checkpoint sourcePanel244Seed_checked sourcePanel244Checkpoint_zero
    sourcePanel244Chunks_checked).trans hlast

theorem sourcePanel244_stream_passes :
    sourcePanelCheck ⟨244, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨244, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨244, by decide⟩)
    sourcePanel244Candidate_stream).trans sourcePanel244Candidate_passes

end ReciprocalXi

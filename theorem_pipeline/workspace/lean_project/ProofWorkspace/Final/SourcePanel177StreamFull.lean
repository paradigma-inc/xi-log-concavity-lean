import ProofWorkspace.Final.SourcePanel177BoundsFull
import ProofWorkspace.Final.SourcePanel177ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel177Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨177, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel177Candidate := by
  have hlast : (sourcePanel177Checkpoint 54).2 = sourcePanel177Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨177, by decide⟩ sourcePanel177Seed
    sourcePanel177Checkpoint sourcePanel177Seed_checked sourcePanel177Checkpoint_zero
    sourcePanel177Chunks_checked).trans hlast

theorem sourcePanel177_stream_passes :
    sourcePanelCheck ⟨177, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨177, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨177, by decide⟩)
    sourcePanel177Candidate_stream).trans sourcePanel177Candidate_passes

end ReciprocalXi

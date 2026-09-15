import ProofWorkspace.Final.SourcePanel134BoundsFull
import ProofWorkspace.Final.SourcePanel134ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel134Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨134, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel134Candidate := by
  have hlast : (sourcePanel134Checkpoint 54).2 = sourcePanel134Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨134, by decide⟩ sourcePanel134Seed
    sourcePanel134Checkpoint sourcePanel134Seed_checked sourcePanel134Checkpoint_zero
    sourcePanel134Chunks_checked).trans hlast

theorem sourcePanel134_stream_passes :
    sourcePanelCheck ⟨134, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨134, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨134, by decide⟩)
    sourcePanel134Candidate_stream).trans sourcePanel134Candidate_passes

end ReciprocalXi

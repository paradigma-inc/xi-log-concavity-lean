import ProofWorkspace.Final.SourcePanel19BoundsFull
import ProofWorkspace.Final.SourcePanel19ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel19Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨19, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel19Candidate := by
  have hlast : (sourcePanel19Checkpoint 54).2 = sourcePanel19Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨19, by decide⟩ sourcePanel19Seed
    sourcePanel19Checkpoint sourcePanel19Seed_checked sourcePanel19Checkpoint_zero
    sourcePanel19Chunks_checked).trans hlast

theorem sourcePanel19_stream_passes :
    sourcePanelCheck ⟨19, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨19, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨19, by decide⟩)
    sourcePanel19Candidate_stream).trans sourcePanel19Candidate_passes

end ReciprocalXi

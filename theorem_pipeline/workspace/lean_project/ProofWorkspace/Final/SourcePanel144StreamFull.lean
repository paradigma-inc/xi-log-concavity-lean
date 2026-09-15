import ProofWorkspace.Final.SourcePanel144BoundsFull
import ProofWorkspace.Final.SourcePanel144ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel144Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨144, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel144Candidate := by
  have hlast : (sourcePanel144Checkpoint 54).2 = sourcePanel144Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨144, by decide⟩ sourcePanel144Seed
    sourcePanel144Checkpoint sourcePanel144Seed_checked sourcePanel144Checkpoint_zero
    sourcePanel144Chunks_checked).trans hlast

theorem sourcePanel144_stream_passes :
    sourcePanelCheck ⟨144, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨144, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨144, by decide⟩)
    sourcePanel144Candidate_stream).trans sourcePanel144Candidate_passes

end ReciprocalXi

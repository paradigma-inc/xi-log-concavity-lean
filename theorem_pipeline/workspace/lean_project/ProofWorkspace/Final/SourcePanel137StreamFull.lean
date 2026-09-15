import ProofWorkspace.Final.SourcePanel137BoundsFull
import ProofWorkspace.Final.SourcePanel137ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel137Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨137, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel137Candidate := by
  have hlast : (sourcePanel137Checkpoint 54).2 = sourcePanel137Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨137, by decide⟩ sourcePanel137Seed
    sourcePanel137Checkpoint sourcePanel137Seed_checked sourcePanel137Checkpoint_zero
    sourcePanel137Chunks_checked).trans hlast

theorem sourcePanel137_stream_passes :
    sourcePanelCheck ⟨137, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨137, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨137, by decide⟩)
    sourcePanel137Candidate_stream).trans sourcePanel137Candidate_passes

end ReciprocalXi

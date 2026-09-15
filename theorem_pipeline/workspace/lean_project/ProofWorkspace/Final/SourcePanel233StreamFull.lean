import ProofWorkspace.Final.SourcePanel233BoundsFull
import ProofWorkspace.Final.SourcePanel233ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel233Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨233, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel233Candidate := by
  have hlast : (sourcePanel233Checkpoint 54).2 = sourcePanel233Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨233, by decide⟩ sourcePanel233Seed
    sourcePanel233Checkpoint sourcePanel233Seed_checked sourcePanel233Checkpoint_zero
    sourcePanel233Chunks_checked).trans hlast

theorem sourcePanel233_stream_passes :
    sourcePanelCheck ⟨233, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨233, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨233, by decide⟩)
    sourcePanel233Candidate_stream).trans sourcePanel233Candidate_passes

end ReciprocalXi

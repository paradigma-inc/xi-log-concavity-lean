import ProofWorkspace.Final.SourcePanel122BoundsFull
import ProofWorkspace.Final.SourcePanel122ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel122Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨122, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel122Candidate := by
  have hlast : (sourcePanel122Checkpoint 54).2 = sourcePanel122Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨122, by decide⟩ sourcePanel122Seed
    sourcePanel122Checkpoint sourcePanel122Seed_checked sourcePanel122Checkpoint_zero
    sourcePanel122Chunks_checked).trans hlast

theorem sourcePanel122_stream_passes :
    sourcePanelCheck ⟨122, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨122, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨122, by decide⟩)
    sourcePanel122Candidate_stream).trans sourcePanel122Candidate_passes

end ReciprocalXi

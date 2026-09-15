import ProofWorkspace.Final.SourcePanel17BoundsFull
import ProofWorkspace.Final.SourcePanel17ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel17Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨17, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel17Candidate := by
  have hlast : (sourcePanel17Checkpoint 54).2 = sourcePanel17Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨17, by decide⟩ sourcePanel17Seed
    sourcePanel17Checkpoint sourcePanel17Seed_checked sourcePanel17Checkpoint_zero
    sourcePanel17Chunks_checked).trans hlast

theorem sourcePanel17_stream_passes :
    sourcePanelCheck ⟨17, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨17, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨17, by decide⟩)
    sourcePanel17Candidate_stream).trans sourcePanel17Candidate_passes

end ReciprocalXi

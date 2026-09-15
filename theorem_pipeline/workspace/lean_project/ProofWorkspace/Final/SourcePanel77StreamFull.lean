import ProofWorkspace.Final.SourcePanel77BoundsFull
import ProofWorkspace.Final.SourcePanel77ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel77Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨77, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel77Candidate := by
  have hlast : (sourcePanel77Checkpoint 54).2 = sourcePanel77Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨77, by decide⟩ sourcePanel77Seed
    sourcePanel77Checkpoint sourcePanel77Seed_checked sourcePanel77Checkpoint_zero
    sourcePanel77Chunks_checked).trans hlast

theorem sourcePanel77_stream_passes :
    sourcePanelCheck ⟨77, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨77, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨77, by decide⟩)
    sourcePanel77Candidate_stream).trans sourcePanel77Candidate_passes

end ReciprocalXi

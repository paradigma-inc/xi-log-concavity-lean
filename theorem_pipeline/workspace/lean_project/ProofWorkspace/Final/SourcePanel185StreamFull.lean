import ProofWorkspace.Final.SourcePanel185BoundsFull
import ProofWorkspace.Final.SourcePanel185ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel185Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨185, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel185Candidate := by
  have hlast : (sourcePanel185Checkpoint 54).2 = sourcePanel185Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨185, by decide⟩ sourcePanel185Seed
    sourcePanel185Checkpoint sourcePanel185Seed_checked sourcePanel185Checkpoint_zero
    sourcePanel185Chunks_checked).trans hlast

theorem sourcePanel185_stream_passes :
    sourcePanelCheck ⟨185, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨185, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨185, by decide⟩)
    sourcePanel185Candidate_stream).trans sourcePanel185Candidate_passes

end ReciprocalXi

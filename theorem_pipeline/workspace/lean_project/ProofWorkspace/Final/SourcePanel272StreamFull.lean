import ProofWorkspace.Final.SourcePanel272BoundsFull
import ProofWorkspace.Final.SourcePanel272ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel272Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨272, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel272Candidate := by
  have hlast : (sourcePanel272Checkpoint 54).2 = sourcePanel272Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨272, by decide⟩ sourcePanel272Seed
    sourcePanel272Checkpoint sourcePanel272Seed_checked sourcePanel272Checkpoint_zero
    sourcePanel272Chunks_checked).trans hlast

theorem sourcePanel272_stream_passes :
    sourcePanelCheck ⟨272, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨272, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨272, by decide⟩)
    sourcePanel272Candidate_stream).trans sourcePanel272Candidate_passes

end ReciprocalXi

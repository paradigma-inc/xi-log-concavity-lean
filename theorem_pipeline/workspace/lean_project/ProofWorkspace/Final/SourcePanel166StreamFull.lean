import ProofWorkspace.Final.SourcePanel166BoundsFull
import ProofWorkspace.Final.SourcePanel166ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel166Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨166, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel166Candidate := by
  have hlast : (sourcePanel166Checkpoint 54).2 = sourcePanel166Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨166, by decide⟩ sourcePanel166Seed
    sourcePanel166Checkpoint sourcePanel166Seed_checked sourcePanel166Checkpoint_zero
    sourcePanel166Chunks_checked).trans hlast

theorem sourcePanel166_stream_passes :
    sourcePanelCheck ⟨166, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨166, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨166, by decide⟩)
    sourcePanel166Candidate_stream).trans sourcePanel166Candidate_passes

end ReciprocalXi

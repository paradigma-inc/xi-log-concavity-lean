import ProofWorkspace.Final.SourcePanel96BoundsFull
import ProofWorkspace.Final.SourcePanel96ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel96Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨96, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel96Candidate := by
  have hlast : (sourcePanel96Checkpoint 54).2 = sourcePanel96Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨96, by decide⟩ sourcePanel96Seed
    sourcePanel96Checkpoint sourcePanel96Seed_checked sourcePanel96Checkpoint_zero
    sourcePanel96Chunks_checked).trans hlast

theorem sourcePanel96_stream_passes :
    sourcePanelCheck ⟨96, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨96, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨96, by decide⟩)
    sourcePanel96Candidate_stream).trans sourcePanel96Candidate_passes

end ReciprocalXi

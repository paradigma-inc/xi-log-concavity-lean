import ProofWorkspace.Final.SourcePanel52BoundsFull
import ProofWorkspace.Final.SourcePanel52ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel52Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨52, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel52Candidate := by
  have hlast : (sourcePanel52Checkpoint 54).2 = sourcePanel52Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨52, by decide⟩ sourcePanel52Seed
    sourcePanel52Checkpoint sourcePanel52Seed_checked sourcePanel52Checkpoint_zero
    sourcePanel52Chunks_checked).trans hlast

theorem sourcePanel52_stream_passes :
    sourcePanelCheck ⟨52, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨52, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨52, by decide⟩)
    sourcePanel52Candidate_stream).trans sourcePanel52Candidate_passes

end ReciprocalXi

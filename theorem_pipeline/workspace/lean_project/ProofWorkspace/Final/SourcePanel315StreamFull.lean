import ProofWorkspace.Final.SourcePanel315BoundsFull
import ProofWorkspace.Final.SourcePanel315ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel315Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨315, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel315Candidate := by
  have hlast : (sourcePanel315Checkpoint 54).2 = sourcePanel315Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨315, by decide⟩ sourcePanel315Seed
    sourcePanel315Checkpoint sourcePanel315Seed_checked sourcePanel315Checkpoint_zero
    sourcePanel315Chunks_checked).trans hlast

theorem sourcePanel315_stream_passes :
    sourcePanelCheck ⟨315, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨315, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨315, by decide⟩)
    sourcePanel315Candidate_stream).trans sourcePanel315Candidate_passes

end ReciprocalXi

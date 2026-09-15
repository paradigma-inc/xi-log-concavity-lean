import ProofWorkspace.Final.SourcePanel61BoundsFull
import ProofWorkspace.Final.SourcePanel61ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel61Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨61, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel61Candidate := by
  have hlast : (sourcePanel61Checkpoint 54).2 = sourcePanel61Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨61, by decide⟩ sourcePanel61Seed
    sourcePanel61Checkpoint sourcePanel61Seed_checked sourcePanel61Checkpoint_zero
    sourcePanel61Chunks_checked).trans hlast

theorem sourcePanel61_stream_passes :
    sourcePanelCheck ⟨61, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨61, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨61, by decide⟩)
    sourcePanel61Candidate_stream).trans sourcePanel61Candidate_passes

end ReciprocalXi

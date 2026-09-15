import ProofWorkspace.Final.SourcePanel259BoundsFull
import ProofWorkspace.Final.SourcePanel259ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel259Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨259, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel259Candidate := by
  have hlast : (sourcePanel259Checkpoint 54).2 = sourcePanel259Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨259, by decide⟩ sourcePanel259Seed
    sourcePanel259Checkpoint sourcePanel259Seed_checked sourcePanel259Checkpoint_zero
    sourcePanel259Chunks_checked).trans hlast

theorem sourcePanel259_stream_passes :
    sourcePanelCheck ⟨259, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨259, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨259, by decide⟩)
    sourcePanel259Candidate_stream).trans sourcePanel259Candidate_passes

end ReciprocalXi

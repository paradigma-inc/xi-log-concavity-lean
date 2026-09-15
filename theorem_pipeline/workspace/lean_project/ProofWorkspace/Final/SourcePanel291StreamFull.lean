import ProofWorkspace.Final.SourcePanel291BoundsFull
import ProofWorkspace.Final.SourcePanel291ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel291Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨291, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel291Candidate := by
  have hlast : (sourcePanel291Checkpoint 54).2 = sourcePanel291Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨291, by decide⟩ sourcePanel291Seed
    sourcePanel291Checkpoint sourcePanel291Seed_checked sourcePanel291Checkpoint_zero
    sourcePanel291Chunks_checked).trans hlast

theorem sourcePanel291_stream_passes :
    sourcePanelCheck ⟨291, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨291, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨291, by decide⟩)
    sourcePanel291Candidate_stream).trans sourcePanel291Candidate_passes

end ReciprocalXi

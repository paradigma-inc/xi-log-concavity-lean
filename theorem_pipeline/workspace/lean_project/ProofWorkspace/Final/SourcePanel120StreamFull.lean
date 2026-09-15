import ProofWorkspace.Final.SourcePanel120BoundsFull
import ProofWorkspace.Final.SourcePanel120ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel120Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨120, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel120Candidate := by
  have hlast : (sourcePanel120Checkpoint 54).2 = sourcePanel120Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨120, by decide⟩ sourcePanel120Seed
    sourcePanel120Checkpoint sourcePanel120Seed_checked sourcePanel120Checkpoint_zero
    sourcePanel120Chunks_checked).trans hlast

theorem sourcePanel120_stream_passes :
    sourcePanelCheck ⟨120, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨120, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨120, by decide⟩)
    sourcePanel120Candidate_stream).trans sourcePanel120Candidate_passes

end ReciprocalXi

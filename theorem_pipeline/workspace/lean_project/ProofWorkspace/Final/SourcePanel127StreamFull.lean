import ProofWorkspace.Final.SourcePanel127BoundsFull
import ProofWorkspace.Final.SourcePanel127ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel127Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨127, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel127Candidate := by
  have hlast : (sourcePanel127Checkpoint 54).2 = sourcePanel127Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨127, by decide⟩ sourcePanel127Seed
    sourcePanel127Checkpoint sourcePanel127Seed_checked sourcePanel127Checkpoint_zero
    sourcePanel127Chunks_checked).trans hlast

theorem sourcePanel127_stream_passes :
    sourcePanelCheck ⟨127, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨127, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨127, by decide⟩)
    sourcePanel127Candidate_stream).trans sourcePanel127Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel260BoundsFull
import ProofWorkspace.Final.SourcePanel260ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel260Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨260, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel260Candidate := by
  have hlast : (sourcePanel260Checkpoint 54).2 = sourcePanel260Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨260, by decide⟩ sourcePanel260Seed
    sourcePanel260Checkpoint sourcePanel260Seed_checked sourcePanel260Checkpoint_zero
    sourcePanel260Chunks_checked).trans hlast

theorem sourcePanel260_stream_passes :
    sourcePanelCheck ⟨260, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨260, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨260, by decide⟩)
    sourcePanel260Candidate_stream).trans sourcePanel260Candidate_passes

end ReciprocalXi

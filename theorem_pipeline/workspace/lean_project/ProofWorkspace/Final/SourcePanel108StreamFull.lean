import ProofWorkspace.Final.SourcePanel108BoundsFull
import ProofWorkspace.Final.SourcePanel108ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel108Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨108, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel108Candidate := by
  have hlast : (sourcePanel108Checkpoint 54).2 = sourcePanel108Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨108, by decide⟩ sourcePanel108Seed
    sourcePanel108Checkpoint sourcePanel108Seed_checked sourcePanel108Checkpoint_zero
    sourcePanel108Chunks_checked).trans hlast

theorem sourcePanel108_stream_passes :
    sourcePanelCheck ⟨108, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨108, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨108, by decide⟩)
    sourcePanel108Candidate_stream).trans sourcePanel108Candidate_passes

end ReciprocalXi

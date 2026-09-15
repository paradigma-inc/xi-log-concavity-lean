import ProofWorkspace.Final.SourcePanel153BoundsFull
import ProofWorkspace.Final.SourcePanel153ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel153Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨153, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel153Candidate := by
  have hlast : (sourcePanel153Checkpoint 54).2 = sourcePanel153Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨153, by decide⟩ sourcePanel153Seed
    sourcePanel153Checkpoint sourcePanel153Seed_checked sourcePanel153Checkpoint_zero
    sourcePanel153Chunks_checked).trans hlast

theorem sourcePanel153_stream_passes :
    sourcePanelCheck ⟨153, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨153, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨153, by decide⟩)
    sourcePanel153Candidate_stream).trans sourcePanel153Candidate_passes

end ReciprocalXi

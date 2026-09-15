import ProofWorkspace.Final.SourcePanel316BoundsFull
import ProofWorkspace.Final.SourcePanel316ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel316Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨316, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel316Candidate := by
  have hlast : (sourcePanel316Checkpoint 54).2 = sourcePanel316Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨316, by decide⟩ sourcePanel316Seed
    sourcePanel316Checkpoint sourcePanel316Seed_checked sourcePanel316Checkpoint_zero
    sourcePanel316Chunks_checked).trans hlast

theorem sourcePanel316_stream_passes :
    sourcePanelCheck ⟨316, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨316, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨316, by decide⟩)
    sourcePanel316Candidate_stream).trans sourcePanel316Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel86BoundsFull
import ProofWorkspace.Final.SourcePanel86ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel86Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨86, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel86Candidate := by
  have hlast : (sourcePanel86Checkpoint 54).2 = sourcePanel86Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨86, by decide⟩ sourcePanel86Seed
    sourcePanel86Checkpoint sourcePanel86Seed_checked sourcePanel86Checkpoint_zero
    sourcePanel86Chunks_checked).trans hlast

theorem sourcePanel86_stream_passes :
    sourcePanelCheck ⟨86, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨86, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨86, by decide⟩)
    sourcePanel86Candidate_stream).trans sourcePanel86Candidate_passes

end ReciprocalXi

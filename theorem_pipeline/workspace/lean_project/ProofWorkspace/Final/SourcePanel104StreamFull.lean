import ProofWorkspace.Final.SourcePanel104BoundsFull
import ProofWorkspace.Final.SourcePanel104ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel104Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨104, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel104Candidate := by
  have hlast : (sourcePanel104Checkpoint 54).2 = sourcePanel104Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨104, by decide⟩ sourcePanel104Seed
    sourcePanel104Checkpoint sourcePanel104Seed_checked sourcePanel104Checkpoint_zero
    sourcePanel104Chunks_checked).trans hlast

theorem sourcePanel104_stream_passes :
    sourcePanelCheck ⟨104, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨104, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨104, by decide⟩)
    sourcePanel104Candidate_stream).trans sourcePanel104Candidate_passes

end ReciprocalXi

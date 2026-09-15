import ProofWorkspace.Final.SourcePanel212BoundsFull
import ProofWorkspace.Final.SourcePanel212ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel212Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨212, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel212Candidate := by
  have hlast : (sourcePanel212Checkpoint 54).2 = sourcePanel212Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨212, by decide⟩ sourcePanel212Seed
    sourcePanel212Checkpoint sourcePanel212Seed_checked sourcePanel212Checkpoint_zero
    sourcePanel212Chunks_checked).trans hlast

theorem sourcePanel212_stream_passes :
    sourcePanelCheck ⟨212, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨212, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨212, by decide⟩)
    sourcePanel212Candidate_stream).trans sourcePanel212Candidate_passes

end ReciprocalXi

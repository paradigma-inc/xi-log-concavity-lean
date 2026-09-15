import ProofWorkspace.Final.SourcePanel314BoundsFull
import ProofWorkspace.Final.SourcePanel314ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel314Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨314, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel314Candidate := by
  have hlast : (sourcePanel314Checkpoint 54).2 = sourcePanel314Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨314, by decide⟩ sourcePanel314Seed
    sourcePanel314Checkpoint sourcePanel314Seed_checked sourcePanel314Checkpoint_zero
    sourcePanel314Chunks_checked).trans hlast

theorem sourcePanel314_stream_passes :
    sourcePanelCheck ⟨314, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨314, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨314, by decide⟩)
    sourcePanel314Candidate_stream).trans sourcePanel314Candidate_passes

end ReciprocalXi

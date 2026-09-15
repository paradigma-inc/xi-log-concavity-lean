import ProofWorkspace.Final.SourcePanel251BoundsFull
import ProofWorkspace.Final.SourcePanel251ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel251Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨251, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel251Candidate := by
  have hlast : (sourcePanel251Checkpoint 54).2 = sourcePanel251Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨251, by decide⟩ sourcePanel251Seed
    sourcePanel251Checkpoint sourcePanel251Seed_checked sourcePanel251Checkpoint_zero
    sourcePanel251Chunks_checked).trans hlast

theorem sourcePanel251_stream_passes :
    sourcePanelCheck ⟨251, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨251, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨251, by decide⟩)
    sourcePanel251Candidate_stream).trans sourcePanel251Candidate_passes

end ReciprocalXi

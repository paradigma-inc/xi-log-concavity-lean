import ProofWorkspace.Final.SourcePanel227BoundsFull
import ProofWorkspace.Final.SourcePanel227ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel227Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨227, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel227Candidate := by
  have hlast : (sourcePanel227Checkpoint 54).2 = sourcePanel227Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨227, by decide⟩ sourcePanel227Seed
    sourcePanel227Checkpoint sourcePanel227Seed_checked sourcePanel227Checkpoint_zero
    sourcePanel227Chunks_checked).trans hlast

theorem sourcePanel227_stream_passes :
    sourcePanelCheck ⟨227, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨227, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨227, by decide⟩)
    sourcePanel227Candidate_stream).trans sourcePanel227Candidate_passes

end ReciprocalXi

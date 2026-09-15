import ProofWorkspace.Final.SourcePanel298BoundsFull
import ProofWorkspace.Final.SourcePanel298ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel298Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨298, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel298Candidate := by
  have hlast : (sourcePanel298Checkpoint 54).2 = sourcePanel298Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨298, by decide⟩ sourcePanel298Seed
    sourcePanel298Checkpoint sourcePanel298Seed_checked sourcePanel298Checkpoint_zero
    sourcePanel298Chunks_checked).trans hlast

theorem sourcePanel298_stream_passes :
    sourcePanelCheck ⟨298, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨298, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨298, by decide⟩)
    sourcePanel298Candidate_stream).trans sourcePanel298Candidate_passes

end ReciprocalXi

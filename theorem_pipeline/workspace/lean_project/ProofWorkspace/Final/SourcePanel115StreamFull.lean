import ProofWorkspace.Final.SourcePanel115BoundsFull
import ProofWorkspace.Final.SourcePanel115ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel115Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨115, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel115Candidate := by
  have hlast : (sourcePanel115Checkpoint 54).2 = sourcePanel115Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨115, by decide⟩ sourcePanel115Seed
    sourcePanel115Checkpoint sourcePanel115Seed_checked sourcePanel115Checkpoint_zero
    sourcePanel115Chunks_checked).trans hlast

theorem sourcePanel115_stream_passes :
    sourcePanelCheck ⟨115, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨115, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨115, by decide⟩)
    sourcePanel115Candidate_stream).trans sourcePanel115Candidate_passes

end ReciprocalXi

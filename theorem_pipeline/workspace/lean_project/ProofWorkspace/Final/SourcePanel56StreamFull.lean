import ProofWorkspace.Final.SourcePanel56BoundsFull
import ProofWorkspace.Final.SourcePanel56ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel56Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨56, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel56Candidate := by
  have hlast : (sourcePanel56Checkpoint 54).2 = sourcePanel56Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨56, by decide⟩ sourcePanel56Seed
    sourcePanel56Checkpoint sourcePanel56Seed_checked sourcePanel56Checkpoint_zero
    sourcePanel56Chunks_checked).trans hlast

theorem sourcePanel56_stream_passes :
    sourcePanelCheck ⟨56, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨56, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨56, by decide⟩)
    sourcePanel56Candidate_stream).trans sourcePanel56Candidate_passes

end ReciprocalXi

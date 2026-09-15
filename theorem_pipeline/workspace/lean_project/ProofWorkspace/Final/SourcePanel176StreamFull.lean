import ProofWorkspace.Final.SourcePanel176BoundsFull
import ProofWorkspace.Final.SourcePanel176ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel176Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨176, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel176Candidate := by
  have hlast : (sourcePanel176Checkpoint 54).2 = sourcePanel176Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨176, by decide⟩ sourcePanel176Seed
    sourcePanel176Checkpoint sourcePanel176Seed_checked sourcePanel176Checkpoint_zero
    sourcePanel176Chunks_checked).trans hlast

theorem sourcePanel176_stream_passes :
    sourcePanelCheck ⟨176, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨176, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨176, by decide⟩)
    sourcePanel176Candidate_stream).trans sourcePanel176Candidate_passes

end ReciprocalXi

import ProofWorkspace.Final.SourcePanel230BoundsFull
import ProofWorkspace.Final.SourcePanel230ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel230Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨230, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel230Candidate := by
  have hlast : (sourcePanel230Checkpoint 54).2 = sourcePanel230Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨230, by decide⟩ sourcePanel230Seed
    sourcePanel230Checkpoint sourcePanel230Seed_checked sourcePanel230Checkpoint_zero
    sourcePanel230Chunks_checked).trans hlast

theorem sourcePanel230_stream_passes :
    sourcePanelCheck ⟨230, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨230, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨230, by decide⟩)
    sourcePanel230Candidate_stream).trans sourcePanel230Candidate_passes

end ReciprocalXi

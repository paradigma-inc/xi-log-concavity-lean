import ProofWorkspace.Final.SourcePanel190BoundsFull
import ProofWorkspace.Final.SourcePanel190ChunkChecksFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

theorem sourcePanel190Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨190, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel190Candidate := by
  have hlast : (sourcePanel190Checkpoint 54).2 = sourcePanel190Candidate := by decide +kernel
  exact (sourcePanelStream_eq_checkpoint ⟨190, by decide⟩ sourcePanel190Seed
    sourcePanel190Checkpoint sourcePanel190Seed_checked sourcePanel190Checkpoint_zero
    sourcePanel190Chunks_checked).trans hlast

theorem sourcePanel190_stream_passes :
    sourcePanelCheck ⟨190, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨190, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨190, by decide⟩)
    sourcePanel190Candidate_stream).trans sourcePanel190Candidate_passes

end ReciprocalXi

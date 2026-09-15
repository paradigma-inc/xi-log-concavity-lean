import ProofWorkspace.Final.SourcePanel317BoundsFull
import ProofWorkspace.Final.SourceMidpointArrayFull
import ProofWorkspace.Final.SourceCoefficientValuesFull
import ProofWorkspace.Final.SourcePanelCompositionFull
import ProofWorkspace.Final.SourcePanel317ChunkChecksFull

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000
namespace ReciprocalXi

/-- Exact equality of the source stream and the checked panel-317 coefficient vector. -/
theorem sourcePanel317Candidate_stream :
    intSourceCoefficientStream (ratSourcePanelCenter ⟨317, by decide⟩)
      sourcePiMidpoint sourceRoundedMidpoint = sourcePanel317Candidate := by
  have hc : ratSourcePanelCenter ⟨317, by decide⟩ = 635/200 := by
    norm_num [ratSourcePanelCenter]
  calc
    intSourceCoefficientStream (ratSourcePanelCenter ⟨317, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint =
        intSourceCoefficientValues (ratSourcePanelCenter ⟨317, by decide⟩)
          sourcePiMidpoint sourceMidpointArray.toList :=
      (intSourceCoefficientValues_array_eq_stream _ _ sourceMidpointArray
        sourceMidpointArray_size).symm
    _ = intSourceCoefficientValues (635/200) sourcePiMidpoint sourceMidpointArray.toList :=
      congrArg (fun c => intSourceCoefficientValues c sourcePiMidpoint
        sourceMidpointArray.toList) hc
    _ = sourcePanel317Candidate :=
      sourcePanel317Values_eq_candidate sourcePanel317Seed_checked sourcePanel317Chunks_checked

theorem sourcePanel317_stream_passes :
    sourcePanelCheck ⟨317, by decide⟩
      (intSourceCoefficientStream (ratSourcePanelCenter ⟨317, by decide⟩)
        sourcePiMidpoint sourceRoundedMidpoint) = true := by
  exact (congrArg (sourcePanelCheck ⟨317, by decide⟩)
    sourcePanel317Candidate_stream).trans sourcePanel317Candidate_passes

end ReciprocalXi

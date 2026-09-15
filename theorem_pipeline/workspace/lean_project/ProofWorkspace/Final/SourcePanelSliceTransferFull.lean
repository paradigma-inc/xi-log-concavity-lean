import ProofWorkspace.Final.SourcePanelCheckpointCompositionFull

set_option autoImplicit false
namespace ReciprocalXi

/-- A certified literal slice may replace the full-array lookup in a transition. -/
theorem sourcePanelChunkCheck_of_slice (seed : ℤ × ℤ)
    (checkpoint : ℕ → SourcePanelCheckpointState) (i : ℕ) (values : List ℚ)
    (hvalues : values = (sourceMidpointArray.toList.drop (256*i)).take
      (min 256 (13601-256*i)))
    (hcheck : (((intSourceTrigStep seed)^[min 256 (13601-256*i)]) (checkpoint i).1,
      intSourceCoefficientValuesFrom sourcePiMidpoint seed 65 (256*i)
        values (checkpoint i).1 (checkpoint i).2) = checkpoint (i+1)) :
    sourcePanelChunkCheck seed checkpoint i := by
  unfold sourcePanelChunkCheck
  simpa only [hvalues] using hcheck

end ReciprocalXi

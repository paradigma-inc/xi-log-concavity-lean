import ProofWorkspace.Final.SourceBlock5216DataFull
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

/-- One whole slice check suffices for the original per-index lookup statement. -/
theorem sourceMidpointSlice_lookup (start count : ℕ) (values : List ℚ)
    (h : values=(sourceMidpointArray.toList.drop start).take count)
    (k : ℕ) (hk : k<count) : values.getD k 0=sourceRoundedMidpoint (start+k) := by
  rw [h,List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hk,List.getElem?_drop]
  simp only [sourceRoundedMidpoint,Array.getD_eq_getD_getElem?,Array.getElem?_toList]

-- A bounded actual-data test, not a changed source or accepted evaluator.
theorem sourceBlock5216Midpoints_slice_checked :
    sourceBlock5216Midpoints=(sourceMidpointArray.toList.drop 5216).take 32 := by
  decide +kernel

theorem sourceBlock5216Midpoints_lookup_via_slice (k : Fin 32) :
    sourceBlock5216Midpoints.getD k 0=sourceRoundedMidpoint (5216+k) :=
  sourceMidpointSlice_lookup 5216 32 sourceBlock5216Midpoints
    sourceBlock5216Midpoints_slice_checked k k.isLt

end ReciprocalXi

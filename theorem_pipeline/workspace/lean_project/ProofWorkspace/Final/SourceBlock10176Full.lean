import ProofWorkspace.Final.SourceBlock10144Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10176DataFull
import ProofWorkspace.Final.EtaBlock10176Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10176XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10176+k) (sourceBlock10176PiPairs.getD k (0,0))
    (sourceEtaBatch10176Lower k, sourceEtaBatch10176Upper k)
    (sourceBlock10176TwoPairs.getD k (0,0))

theorem sourceBlock10176Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10176XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10176+k):ℂ)).re ∧
      (xi (xiGridArgument (10176+k):ℂ)).re ≤ ((sourceBlock10176XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10176+k) _ _ _
    (sourceBlock10176PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10176_actual_enclosure k hk)
    (sourceBlock10176TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10176Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10176XiPair k).1 := by
  decide +kernel

theorem sourceBlock10176Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10176Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10176XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10176XiPair k)).2 ≤
      sourceBlock10176Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10176_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10176+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10176+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10176Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10176+k) (sourceBlock10176XiPair k) _
    (sourceBlock10176Xi_enclosure k hk) (sourceBlock10176Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10176Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10208_bound (k : ℕ) (hk : k < 10208) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10176
  · exact sourceRoundedMidpoint_first10176_bound k h
  · have hsum : 10176+(k-10176) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10176_bound (k-10176) (by omega)

end ReciprocalXi

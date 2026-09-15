import ProofWorkspace.Final.SourceBlock10336Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10368DataFull
import ProofWorkspace.Final.EtaBlock10368Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10368XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10368+k) (sourceBlock10368PiPairs.getD k (0,0))
    (sourceEtaBatch10368Lower k, sourceEtaBatch10368Upper k)
    (sourceBlock10368TwoPairs.getD k (0,0))

theorem sourceBlock10368Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10368XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10368+k):ℂ)).re ∧
      (xi (xiGridArgument (10368+k):ℂ)).re ≤ ((sourceBlock10368XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10368+k) _ _ _
    (sourceBlock10368PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10368_actual_enclosure k hk)
    (sourceBlock10368TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10368Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10368XiPair k).1 := by
  decide +kernel

theorem sourceBlock10368Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10368Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10368XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10368XiPair k)).2 ≤
      sourceBlock10368Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10368_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10368+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10368+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10368Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10368+k) (sourceBlock10368XiPair k) _
    (sourceBlock10368Xi_enclosure k hk) (sourceBlock10368Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10368Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10400_bound (k : ℕ) (hk : k < 10400) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10368
  · exact sourceRoundedMidpoint_first10368_bound k h
  · have hsum : 10368+(k-10368) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10368_bound (k-10368) (by omega)

end ReciprocalXi

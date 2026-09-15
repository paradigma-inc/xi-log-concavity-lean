import ProofWorkspace.Final.SourceBlock13408Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13440DataFull
import ProofWorkspace.Final.EtaBlock13440Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13440XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13440+k) (sourceBlock13440PiPairs.getD k (0,0))
    (sourceEtaBatch13440Lower k, sourceEtaBatch13440Upper k)
    (sourceBlock13440TwoPairs.getD k (0,0))

theorem sourceBlock13440Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13440XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13440+k):ℂ)).re ∧
      (xi (xiGridArgument (13440+k):ℂ)).re ≤ ((sourceBlock13440XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13440+k) _ _ _
    (sourceBlock13440PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13440_actual_enclosure k hk)
    (sourceBlock13440TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13440Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13440XiPair k).1 := by
  decide +kernel

theorem sourceBlock13440Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13440Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13440XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13440XiPair k)).2 ≤
      sourceBlock13440Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13440_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13440+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13440+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13440Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13440+k) (sourceBlock13440XiPair k) _
    (sourceBlock13440Xi_enclosure k hk) (sourceBlock13440Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13440Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13472_bound (k : ℕ) (hk : k < 13472) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13440
  · exact sourceRoundedMidpoint_first13440_bound k h
  · have hsum : 13440+(k-13440) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13440_bound (k-13440) (by omega)

end ReciprocalXi

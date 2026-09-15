import ProofWorkspace.Final.SourceBlock13120Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13152DataFull
import ProofWorkspace.Final.EtaBlock13152Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13152XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13152+k) (sourceBlock13152PiPairs.getD k (0,0))
    (sourceEtaBatch13152Lower k, sourceEtaBatch13152Upper k)
    (sourceBlock13152TwoPairs.getD k (0,0))

theorem sourceBlock13152Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13152XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13152+k):ℂ)).re ∧
      (xi (xiGridArgument (13152+k):ℂ)).re ≤ ((sourceBlock13152XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13152+k) _ _ _
    (sourceBlock13152PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13152_actual_enclosure k hk)
    (sourceBlock13152TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13152Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13152XiPair k).1 := by
  decide +kernel

theorem sourceBlock13152Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13152Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13152XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13152XiPair k)).2 ≤
      sourceBlock13152Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13152_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13152+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13152+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13152Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13152+k) (sourceBlock13152XiPair k) _
    (sourceBlock13152Xi_enclosure k hk) (sourceBlock13152Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13152Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13184_bound (k : ℕ) (hk : k < 13184) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13152
  · exact sourceRoundedMidpoint_first13152_bound k h
  · have hsum : 13152+(k-13152) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13152_bound (k-13152) (by omega)

end ReciprocalXi

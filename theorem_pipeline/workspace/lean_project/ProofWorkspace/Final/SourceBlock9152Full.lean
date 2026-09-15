import ProofWorkspace.Final.SourceBlock9120Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9152DataFull
import ProofWorkspace.Final.EtaBlock9152Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9152XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9152+k) (sourceBlock9152PiPairs.getD k (0,0))
    (sourceEtaBatch9152Lower k, sourceEtaBatch9152Upper k)
    (sourceBlock9152TwoPairs.getD k (0,0))

theorem sourceBlock9152Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9152XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9152+k):ℂ)).re ∧
      (xi (xiGridArgument (9152+k):ℂ)).re ≤ ((sourceBlock9152XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9152+k) _ _ _
    (sourceBlock9152PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9152_actual_enclosure k hk)
    (sourceBlock9152TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9152Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9152XiPair k).1 := by
  decide +kernel

theorem sourceBlock9152Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9152Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9152XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9152XiPair k)).2 ≤
      sourceBlock9152Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9152_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9152+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9152+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9152Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9152+k) (sourceBlock9152XiPair k) _
    (sourceBlock9152Xi_enclosure k hk) (sourceBlock9152Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9152Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9184_bound (k : ℕ) (hk : k < 9184) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9152
  · exact sourceRoundedMidpoint_first9152_bound k h
  · have hsum : 9152+(k-9152) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9152_bound (k-9152) (by omega)

end ReciprocalXi

import ProofWorkspace.Final.FirstSourceBlockDataFull
import ProofWorkspace.Final.EtaBatchSixtyFourFull

set_option autoImplicit false
set_option maxRecDepth 32768
namespace ReciprocalXi

def sourceFirstEtaPair (k : ℕ) : ℚ × ℚ :=
  if k < 32 then (sourceEtaBatch0Lower k, sourceEtaBatch0Upper k)
  else if k < 64 then (sourceEtaBatch32Lower (k-32), sourceEtaBatch32Upper (k-32))
  else (sourceEtaBatch64Lower (k-64), sourceEtaBatch64Upper (k-64))

theorem sourceFirstEta_enclosure (k : ℕ) (hk : k < 160) :
    ((sourceFirstEtaPair k).1:ℝ) ≤ etaIntegral (xiGridArgument k:ℝ) ∧
      etaIntegral (xiGridArgument k:ℝ) ≤ ((sourceFirstEtaPair k).2:ℝ) := by
  unfold sourceFirstEtaPair
  split_ifs with h0 h1
  · exact sourceEtaBatch0_actual_enclosure k h0
  · have he : 32+(k-32) = k := by omega
    simpa only [he] using sourceEtaBatch32_actual_enclosure (k-32) (by omega)
  · have he : 64+(k-64) = k := by omega
    simpa only [he] using sourceEtaBatch64_actual_enclosure (k-64) (by omega)

theorem sourceFirstPi_enclosure (k : ℕ) (hk : k < 160) :
    ((sourceFirstPiPairs.getD k (0,0)).1:ℝ) ≤ Real.pi^(-(xiGridArgument k:ℝ)/2) ∧
      Real.pi^(-(xiGridArgument k:ℝ)/2) ≤ ((sourceFirstPiPairs.getD k (0,0)).2:ℝ) := by
  rw [←sourceFirstPiPairs_eq ⟨k,hk⟩]
  exact sourcePiRoot_grid_enclosure k

theorem sourceFirstTwo_enclosure (k : ℕ) (hk : k < 160) :
    ((sourceFirstTwoPairs.getD k (0,0)).1:ℝ) ≤ (2:ℝ)^(-(xiGridArgument k:ℝ)) ∧
      (2:ℝ)^(-(xiGridArgument k:ℝ)) ≤ ((sourceFirstTwoPairs.getD k (0,0)).2:ℝ) := by
  rw [←sourceFirstTwoPairs_eq ⟨k,hk⟩]
  exact retainedTwo_enclosure k

def sourceGammaResidueIndex (k : ℕ) : ℕ :=
  if k < 40 then k+120 else (k-40)%160

theorem sourceGammaResidueIndex_lt (k : ℕ) : sourceGammaResidueIndex k < 160 := by
  unfold sourceGammaResidueIndex
  split_ifs with hk
  · omega
  · exact Nat.mod_lt _ (by decide)

theorem gammaGridOffset_eq_residue (k : ℕ) :
    gammaGridOffset k = ((sourceGammaResidueIndex k:ℤ)-80:ℚ)/160 := by
  unfold gammaGridOffset sourceGammaResidueIndex
  split_ifs with hk
  · unfold gammaGridArgument
    push_cast
    ring
  · unfold gammaGridBase
    simp only [Int.cast_natCast]
    ring

end ReciprocalXi

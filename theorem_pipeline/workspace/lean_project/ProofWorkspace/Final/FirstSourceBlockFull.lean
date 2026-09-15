import ProofWorkspace.Final.FirstSourceBlockFactorsFull
import ProofWorkspace.Final.GammaOffsetExpFull
import ProofWorkspace.Final.RootDenominatorPositiveFull
import ProofWorkspace.Final.SourceMidpointArrayFull

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceFirstGammaPair (k : ℕ) : ℚ × ℚ :=
  let g := sourceGammaExpPairs.getD (sourceGammaResidueIndex k) (0,0)
  (ratRoundLower (gammaGridMultiplier k*g.1) (10^180),
    ratRoundUpper (gammaGridMultiplier k*g.2) (10^180))

theorem sourceFirstGamma_eq_retained (k : ℕ) :
    sourceFirstGammaPair k = (retainedGammaLower k, retainedGammaUpper k) := by
  unfold sourceFirstGammaPair
  rw [sourceGammaExpPairs_eq_fast ⟨sourceGammaResidueIndex k, sourceGammaResidueIndex_lt k⟩]
  have he : gammaOffsetResidue (sourceGammaResidueIndex k) = gammaGridOffset k := by
    exact (gammaGridOffset_eq_residue k).symm
  rw [he]
  rfl

theorem sourceFirstGamma_enclosure (k : ℕ) :
    ((sourceFirstGammaPair k).1:ℝ) ≤ Real.Gamma ((xiGridArgument k:ℝ)/2) ∧
      Real.Gamma ((xiGridArgument k:ℝ)/2) ≤ ((sourceFirstGammaPair k).2:ℝ) := by
  rw [sourceFirstGamma_eq_retained]
  exact retainedGamma_enclosure k

def sourceFirstBracketPair (k : ℕ) : ℚ × ℚ :=
  let t := sourceFirstTwoPairs.getD k (0,0)
  (ratRootBracketLower (xiGridArgument k) t.1 t.2,
    ratRootBracketUpper (xiGridArgument k) t.1 t.2)

theorem sourceFirstBracket_enclosure (k : ℕ) (hk : k < 160) (hne : k ≠ 40) :
    ((sourceFirstBracketPair k).1:ℝ) ≤ xiEtaBracket (xiGridArgument k:ℝ) ∧
      xiEtaBracket (xiGridArgument k:ℝ) ≤ ((sourceFirstBracketPair k).2:ℝ) := by
  unfold sourceFirstBracketPair
  rw [←sourceFirstTwoPairs_eq ⟨k,hk⟩]
  exact retainedBracket_enclosure k hne (retainedRoot_denominator_pos k hne)

def sourceFirstXiPair (k : ℕ) : ℚ × ℚ :=
  if k=40 then (1/2,1/2) else
    let g := sourceFirstGammaPair k
    let p := sourceFirstPiPairs.getD k (0,0)
    let e := sourceFirstEtaPair k
    let b := sourceFirstBracketPair k
    (ratFactorXiLower (xiGridArgument k) g.1 p.1 e.1 b.1 (10^180),
      ratFactorXiUpper (xiGridArgument k) g.2 p.2 e.2 b.2 (10^180))

theorem sourceFirstXi_enclosure (k : ℕ) (hk : k < 160) :
    ((sourceFirstXiPair k).1:ℝ) ≤ (xi (xiGridArgument k:ℂ)).re ∧
      (xi (xiGridArgument k:ℂ)).re ≤ ((sourceFirstXiPair k).2:ℝ) := by
  by_cases hne : k=40
  · subst k
    norm_num [sourceFirstXiPair, xiGridArgument, xi_one]
  · unfold sourceFirstXiPair
    rw [if_neg hne]
    exact ratFactorXi_enclosure _ _ _ _ _ _ _ _ _ _ (xiGridArgument_pos k)
      (xiGridArgument_ne_one k hne) (by norm_num) (sourceFirstGamma_enclosure k)
      (sourceFirstPi_enclosure k hk) (sourceFirstEta_enclosure k hk)
      (sourceFirstBracket_enclosure k hk hne)

def sourceFirstReciprocalPair (k : ℕ) : ℚ × ℚ :=
  let x := sourceFirstXiPair k
  (ratRoundLower (max 0 candidateXiZeroValues.1/x.2) (10^180),
    ratRoundUpper (candidateXiZeroValues.2/x.1) (10^180))

theorem sourceFirstXi_positive_checked : ∀ k : Fin 160, 0 < (sourceFirstXiPair k).1 := by
  decide +kernel

theorem sourceFirstReciprocal_enclosure (k : ℕ) (hk : k < 160) :
    ((sourceFirstReciprocalPair k).1:ℝ) ≤ (reciprocalTransform ((k:ℝ)/40)).re ∧
      (reciprocalTransform ((k:ℝ)/40)).re ≤ ((sourceFirstReciprocalPair k).2:ℝ) := by
  have hD := sourceFirstXi_enclosure k hk
  have hN := xiCentral_certified_candidate_enclosure
  have hdR : 0 < ((sourceFirstXiPair k).1:ℝ) := by
    exact_mod_cast sourceFirstXi_positive_checked ⟨k,hk⟩
  have hden := hdR.trans_le hD.1
  have hupper := hden.trans_le hD.2
  have hnum : 0 ≤ (xi (1/2)).re := by
    have h := (xi_re_pos (1/2)).le
    norm_num at h
    exact h
  have hmax := max_le hnum hN.1
  have he : (reciprocalTransform ((k:ℝ)/40)).re =
      (xi (1/2)).re/(xi (xiGridArgument k:ℂ)).re := by
    have h := reciprocalTransform_grid_re k
    norm_num only [xiGridArgument, Nat.cast_zero, zero_add] at h ⊢
    norm_num at h ⊢
    exact h
  unfold sourceFirstReciprocalPair
  apply ratRound_interval_enclosure _ _ _ (10^180) (by norm_num)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hmax hupper.le).trans
      (div_le_div_of_nonneg_left hnum hden hD.2)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hN.2 hden.le).trans
      (div_le_div_of_nonneg_left (hnum.trans hN.2) hdR hD.1)

theorem sourceFirstMidpoint_check : ∀ k : Fin 160,
    sourceFirstMidpoints.getD k 0-2/(10:ℚ)^120 ≤ (sourceFirstReciprocalPair k).1 ∧
      (sourceFirstReciprocalPair k).2 ≤ sourceFirstMidpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceFirstMidpoint_actual_bound (k : ℕ) (hk : k < 160) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceFirstMidpoints.getD k 0:ℝ)| ≤
      2/(10:ℝ)^120 := by
  have h := sourceFirstReciprocal_enclosure k hk
  have hv := sourceFirstMidpoint_check ⟨k,hk⟩
  have hl : ((sourceFirstMidpoints.getD k 0-2/(10:ℚ)^120:ℚ):ℝ) ≤
      ((sourceFirstReciprocalPair k).1:ℝ) := Rat.cast_le.mpr hv.1
  have hu : ((sourceFirstReciprocalPair k).2:ℝ) ≤
      ((sourceFirstMidpoints.getD k 0+2/(10:ℚ)^120:ℚ):ℝ) := Rat.cast_le.mpr hv.2
  push_cast at hl hu
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

theorem sourceFirstMidpoints_eq_array : ∀ k : Fin 160,
    sourceFirstMidpoints.getD k 0 = sourceRoundedMidpoint k := by
  decide +kernel

theorem sourceRoundedMidpoint_first160_bound (k : ℕ) (hk : k < 160) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  rw [←sourceFirstMidpoints_eq_array ⟨k,hk⟩]
  exact sourceFirstMidpoint_actual_bound k hk

end ReciprocalXi

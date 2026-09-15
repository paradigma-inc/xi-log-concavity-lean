import ProofWorkspace.Final.FirstSourceBlockFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

/-- Assemble stored power and eta endpoints with the certified reusable Gamma table. -/
def sourceGridXiPair (k : ℕ) (p e t : ℚ × ℚ) : ℚ × ℚ :=
  if k=40 then (1/2,1/2) else
    let g := sourceFirstGammaPair k
    let b := (ratRootBracketLower (xiGridArgument k) t.1 t.2,
      ratRootBracketUpper (xiGridArgument k) t.1 t.2)
    (ratFactorXiLower (xiGridArgument k) g.1 p.1 e.1 b.1 (10^180),
      ratFactorXiUpper (xiGridArgument k) g.2 p.2 e.2 b.2 (10^180))

theorem sourceGridXi_enclosure (k : ℕ) (p e t : ℚ × ℚ)
    (hp : p = (retainedPiLower k, retainedPiUpper k))
    (he : (e.1:ℝ) ≤ etaIntegral (xiGridArgument k:ℝ) ∧
      etaIntegral (xiGridArgument k:ℝ) ≤ (e.2:ℝ))
    (ht : t = (retainedTwoLower k, retainedTwoUpper k)) :
    ((sourceGridXiPair k p e t).1:ℝ) ≤ (xi (xiGridArgument k:ℂ)).re ∧
      (xi (xiGridArgument k:ℂ)).re ≤ ((sourceGridXiPair k p e t).2:ℝ) := by
  subst p t
  by_cases hne : k=40
  · subst k
    norm_num [sourceGridXiPair, xiGridArgument, xi_one]
  · unfold sourceGridXiPair
    rw [if_neg hne]
    exact ratFactorXi_enclosure _ _ _ _ _ _ _ _ _ _ (xiGridArgument_pos k)
      (xiGridArgument_ne_one k hne) (by norm_num) (sourceFirstGamma_enclosure k)
      (sourcePiRoot_grid_enclosure k) he
      (retainedBracket_enclosure k hne (retainedRoot_denominator_pos k hne))

def sourceGridReciprocalPair (x : ℚ × ℚ) : ℚ × ℚ :=
  (ratRoundLower (max 0 candidateXiZeroValues.1/x.2) (10^180),
    ratRoundUpper (candidateXiZeroValues.2/x.1) (10^180))

theorem sourceGridReciprocal_enclosure (k : ℕ) (x : ℚ × ℚ)
    (hX : (x.1:ℝ) ≤ (xi (xiGridArgument k:ℂ)).re ∧
      (xi (xiGridArgument k:ℂ)).re ≤ (x.2:ℝ)) (hx : 0 < x.1) :
    ((sourceGridReciprocalPair x).1:ℝ) ≤ (reciprocalTransform ((k:ℝ)/40)).re ∧
      (reciprocalTransform ((k:ℝ)/40)).re ≤ ((sourceGridReciprocalPair x).2:ℝ) := by
  have hN := xiCentral_certified_candidate_enclosure
  have hdR : 0 < (x.1:ℝ) := by exact_mod_cast hx
  have hden := hdR.trans_le hX.1
  have hupper := hden.trans_le hX.2
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
  unfold sourceGridReciprocalPair
  apply ratRound_interval_enclosure _ _ _ (10^180) (by norm_num)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hmax hupper.le).trans
      (div_le_div_of_nonneg_left hnum hden hX.2)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hN.2 hden.le).trans
      (div_le_div_of_nonneg_left (hnum.trans hN.2) hdR hX.1)

theorem sourceGridMidpoint_actual_bound (k : ℕ) (x : ℚ × ℚ) (v : ℚ)
    (hX : (x.1:ℝ) ≤ (xi (xiGridArgument k:ℂ)).re ∧
      (xi (xiGridArgument k:ℂ)).re ≤ (x.2:ℝ)) (hx : 0 < x.1)
    (hv : v-2/(10:ℚ)^120 ≤ (sourceGridReciprocalPair x).1 ∧
      (sourceGridReciprocalPair x).2 ≤ v+2/(10:ℚ)^120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(v:ℝ)| ≤ 2/(10:ℝ)^120 := by
  have h := sourceGridReciprocal_enclosure k x hX hx
  have hl : ((v-2/(10:ℚ)^120:ℚ):ℝ) ≤ ((sourceGridReciprocalPair x).1:ℝ) :=
    Rat.cast_le.mpr hv.1
  have hu : ((sourceGridReciprocalPair x).2:ℝ) ≤ ((v+2/(10:ℚ)^120:ℚ):ℝ) :=
    Rat.cast_le.mpr hv.2
  push_cast at hl hu
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

end ReciprocalXi

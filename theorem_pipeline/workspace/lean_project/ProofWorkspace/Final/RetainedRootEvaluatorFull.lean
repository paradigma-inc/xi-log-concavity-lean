import ProofWorkspace.Final.PiRootSeedFull
import ProofWorkspace.Final.SpecialSourceSamplesFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def retainedPiLower (k : ℕ) : ℚ :=
  ratPowRoundLower sourcePiRootLower (10^180) (k+40)
def retainedPiUpper (k : ℕ) : ℚ :=
  ratPowRoundUpper sourcePiRootUpper (10^180) (k+40)
def retainedTwoLower (k : ℕ) : ℚ :=
  ratPowRoundLower (rootLowerFor 2) (10^180) (k+40)
def retainedTwoUpper (k : ℕ) : ℚ :=
  ratPowRoundUpper (rootUpperFor 2) (10^180) (k+40)
def retainedGammaLower (k : ℕ) : ℚ :=
  ratGammaGridFastLower k 440 480 400 256 128 (10^180)
def retainedGammaUpper (k : ℕ) : ℚ :=
  ratGammaGridFastUpper k 440 480 400 256 128 (10^180)
def retainedEtaLower (k : ℕ) : ℚ :=
  ratEtaRootGridLower 400 k (10^180) rootLowerFor rootUpperFor
def retainedEtaUpper (k : ℕ) : ℚ :=
  ratEtaRootGridUpper 400 k (10^180) rootLowerFor rootUpperFor
def retainedBracketLower (k : ℕ) : ℚ :=
  ratRootBracketLower (xiGridArgument k) (retainedTwoLower k) (retainedTwoUpper k)
def retainedBracketUpper (k : ℕ) : ℚ :=
  ratRootBracketUpper (xiGridArgument k) (retainedTwoLower k) (retainedTwoUpper k)

theorem retainedTwo_enclosure (k : ℕ) :
    (retainedTwoLower k:ℝ) ≤ (2:ℝ)^(-(xiGridArgument k:ℝ)) ∧
      (2:ℝ)^(-(xiGridArgument k:ℝ)) ≤ (retainedTwoUpper k:ℝ) := by
  have hc := rootPowerGridBounds 2 (by norm_num) (by norm_num)
  have h := ratRoot80Grid_enclosure 2 (rootLowerFor 2) (rootUpperFor 2) k (10^180)
    (by norm_num) (by norm_num) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  simpa only [Rat.cast_ofNat] using h

theorem retainedGamma_enclosure (k : ℕ) :
    (retainedGammaLower k:ℝ) ≤ Real.Gamma ((xiGridArgument k:ℝ)/2) ∧
      Real.Gamma ((xiGridArgument k:ℝ)/2) ≤ (retainedGammaUpper k:ℝ) := by
  have hc := firstNode_gamma_checks k
  have h := ratGammaGridFast_enclosure k 440 480 400 256 128 (10^180)
    (by norm_num) (by norm_num) (by norm_num) hc.1 hc.2
  have he : (gammaGridArgument k:ℝ) = (xiGridArgument k:ℝ)/2 := by
    have hr := congrArg (fun q:ℚ => (q:ℝ)) (xiGridArgument_half k)
    push_cast at hr
    exact hr.symm
  rw [he] at h
  exact h

theorem retainedEta_enclosure (k : ℕ) :
    (retainedEtaLower k:ℝ) ≤ etaIntegral (xiGridArgument k:ℝ) ∧
      etaIntegral (xiGridArgument k:ℝ) ≤ (retainedEtaUpper k:ℝ) :=
  ratEtaRootGrid_enclosure 400 k (10^180) rootLowerFor rootUpperFor
    (by norm_num) firstNode_root_checks

theorem retainedBracket_enclosure (k : ℕ) (hk : k ≠ 40)
    (hd : 0 < ratRootDenominatorLower (xiGridArgument k)
      (retainedTwoLower k) (retainedTwoUpper k)) :
    (retainedBracketLower k:ℝ) ≤ xiEtaBracket (xiGridArgument k:ℝ) ∧
      xiEtaBracket (xiGridArgument k:ℝ) ≤ (retainedBracketUpper k:ℝ) :=
  ratRootBracket_enclosure (xiGridArgument k) (retainedTwoLower k) (retainedTwoUpper k)
    (xiGridArgument_ne_one k hk) (retainedTwo_enclosure k).1 (retainedTwo_enclosure k).2 hd

def retainedRootXiLower (k : ℕ) : ℚ :=
  if k=40 then 1/2 else ratFactorXiLower (xiGridArgument k)
    (retainedGammaLower k) (retainedPiLower k) (retainedEtaLower k) (retainedBracketLower k) (10^180)
def retainedRootXiUpper (k : ℕ) : ℚ :=
  if k=40 then 1/2 else ratFactorXiUpper (xiGridArgument k)
    (retainedGammaUpper k) (retainedPiUpper k) (retainedEtaUpper k) (retainedBracketUpper k) (10^180)

theorem retainedRootXi_enclosure (k : ℕ)
    (hd : k ≠ 40 → 0 < ratRootDenominatorLower (xiGridArgument k)
      (retainedTwoLower k) (retainedTwoUpper k)) :
    (retainedRootXiLower k:ℝ) ≤ (xi (xiGridArgument k:ℂ)).re ∧
      (xi (xiGridArgument k:ℂ)).re ≤ (retainedRootXiUpper k:ℝ) := by
  by_cases hk : k=40
  · subst k
    norm_num [retainedRootXiLower, retainedRootXiUpper, xiGridArgument, xi_one]
  · unfold retainedRootXiLower retainedRootXiUpper
    rw [if_neg hk, if_neg hk]
    exact ratFactorXi_enclosure _ _ _ _ _ _ _ _ _ _ (xiGridArgument_pos k)
      (xiGridArgument_ne_one k hk) (by norm_num) (retainedGamma_enclosure k)
      (sourcePiRoot_grid_enclosure k) (retainedEta_enclosure k)
      (retainedBracket_enclosure k hk (hd hk))

def retainedReciprocalLower (k : ℕ) : ℚ :=
  ratRoundLower (max 0 candidateXiZeroValues.1 / retainedRootXiUpper k) (10^180)
def retainedReciprocalUpper (k : ℕ) : ℚ :=
  ratRoundUpper (candidateXiZeroValues.2 / retainedRootXiLower k) (10^180)

theorem retainedReciprocal_enclosure (k : ℕ)
    (hb : k ≠ 40 → 0 < ratRootDenominatorLower (xiGridArgument k)
      (retainedTwoLower k) (retainedTwoUpper k))
    (hd : 0 < retainedRootXiLower k) :
    (retainedReciprocalLower k:ℝ) ≤ (reciprocalTransform ((k:ℝ)/40)).re ∧
      (reciprocalTransform ((k:ℝ)/40)).re ≤ (retainedReciprocalUpper k:ℝ) := by
  have hD := retainedRootXi_enclosure k hb
  have hN := xiCentral_certified_candidate_enclosure
  have hdR : 0 < (retainedRootXiLower k:ℝ) := by exact_mod_cast hd
  have hden := hdR.trans_le hD.1
  have hupper := hden.trans_le hD.2
  have hnum : 0 ≤ (xi (1/2)).re := by
    have h := (xi_re_pos (1/2)).le
    norm_num at h
    exact h
  have hmax := max_le hnum hN.1
  have he : (reciprocalTransform ((k:ℝ)/40)).re =
      (xi (1/2)).re / (xi (xiGridArgument k:ℂ)).re := by
    have h := reciprocalTransform_grid_re k
    norm_num only [xiGridArgument, Nat.cast_zero, zero_add] at h ⊢
    norm_num at h ⊢
    exact h
  unfold retainedReciprocalLower retainedReciprocalUpper
  apply ratRound_interval_enclosure _ _ _ (10^180) (by norm_num)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hmax hupper.le).trans
      (div_le_div_of_nonneg_left hnum hden hD.2)
  · push_cast
    rw [he]
    exact (div_le_div_of_nonneg_right hN.2 hden.le).trans
      (div_le_div_of_nonneg_left (hnum.trans hN.2) hdR hD.1)

theorem retainedSourceMidpoint_bound (k : ℕ) (v : ℚ)
    (hb : k ≠ 40 → 0 < ratRootDenominatorLower (xiGridArgument k)
      (retainedTwoLower k) (retainedTwoUpper k))
    (hd : 0 < retainedRootXiLower k)
    (hv : v-2/(10:ℚ)^120 ≤ retainedReciprocalLower k ∧
      retainedReciprocalUpper k ≤ v+2/(10:ℚ)^120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(v:ℝ)| ≤ 2/(10:ℝ)^120 := by
  have h := retainedReciprocal_enclosure k hb hd
  have hl : ((v-2/(10:ℚ)^120:ℚ):ℝ) ≤ (retainedReciprocalLower k:ℝ) := Rat.cast_le.mpr hv.1
  have hu : (retainedReciprocalUpper k:ℝ) ≤ ((v+2/(10:ℚ)^120:ℚ):ℝ) := Rat.cast_le.mpr hv.2
  push_cast at hl hu
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

end ReciprocalXi


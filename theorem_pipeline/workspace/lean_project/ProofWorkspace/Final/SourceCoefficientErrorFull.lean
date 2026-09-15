import ProofWorkspace.Final.SourceTrigBoundsFull
import ProofWorkspace.Final.RationalRoundingBoundsFull

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def sourceWeightMultiplier (j k : ℕ) : ℚ := (k:ℚ)/(8000*(j+1:ℕ))

def ratSourceRoundedWeight (p : ℚ) (v : ℕ → ℚ) (B : ℕ) : ℕ → ℕ → ℚ
  | 0, k => ratRoundLower ((1/(40*p))*v k*(if k=0 then 1/2 else 1)) B
  | j+1, k => ratRoundLower (ratSourceRoundedWeight p v B j k*sourceWeightMultiplier j k) B

private theorem ratRoundLower_error_real (q : ℚ) (B : ℕ) (hB : 0 < B) :
    |(ratRoundLower q B:ℝ)-(q:ℝ)| ≤ 1/(B:ℝ) := by
  have h := ratRound_real_enclosure q B hB
  have hw := ratRound_width_le q B hB
  have hw' : (ratRoundUpper q B:ℝ)-(ratRoundLower q B:ℝ) ≤ 1/(B:ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr hw
  rw [abs_of_nonpos (sub_nonpos.mpr h.1)]
  linarith [h.2]

theorem sourceWeightMultiplier_bounds (j k : ℕ) (hk : k ≤ 13600) :
    0 ≤ (sourceWeightMultiplier j k:ℝ) ∧ (sourceWeightMultiplier j k:ℝ) ≤ 2 := by
  have hk' : (k:ℝ) ≤ 13600 := by exact_mod_cast hk
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
  unfold sourceWeightMultiplier
  push_cast
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<8000*((j:ℝ)+1))).mpr
    linarith

private theorem sourceCoefficientWeight_multiplier (p : ℝ) (v : ℕ → ℝ) (j k : ℕ) :
    sourceCoefficientWeight p v (j+1) k =
      sourceCoefficientWeight p v j k * (sourceWeightMultiplier j k:ℝ) := by
  rw [sourceCoefficientWeight_succ]
  unfold sourceWeightMultiplier
  push_cast
  field_simp

theorem ratSourceRoundedWeight_error (p : ℚ) (v : ℕ → ℚ) (B j k : ℕ)
    (hB : 0 < B) (hk : k ≤ 13600) :
    |(ratSourceRoundedWeight p v B j k:ℝ)-
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k| ≤
      ((2:ℝ)^(j+1)-1)/(B:ℝ) := by
  induction j with
  | zero =>
    have h := ratRoundLower_error_real ((1/(40*p))*v k*(if k=0 then 1/2 else 1)) B hB
    by_cases hk0 : k=0
    · simpa [ratSourceRoundedWeight, sourceCoefficientWeight, hk0, show (2:ℝ)-1=1 by norm_num] using h
    · simpa [ratSourceRoundedWeight, sourceCoefficientWeight, hk0, show (2:ℝ)-1=1 by norm_num] using h
  | succ j ih =>
    have hmul := sourceWeightMultiplier_bounds j k hk
    have hr := ratRoundLower_error_real
      (ratSourceRoundedWeight p v B j k*sourceWeightMultiplier j k) B hB
    have hmabs : |(sourceWeightMultiplier j k:ℝ)| ≤ 2 := by
      rw [abs_of_nonneg hmul.1]
      exact hmul.2
    have he : (ratSourceRoundedWeight p v B (j+1) k:ℝ)-
        sourceCoefficientWeight p (fun k => (v k:ℝ)) (j+1) k =
        ((ratSourceRoundedWeight p v B (j+1) k:ℝ)-
          (ratSourceRoundedWeight p v B j k:ℝ)*(sourceWeightMultiplier j k:ℝ))+
        ((ratSourceRoundedWeight p v B j k:ℝ)-
          sourceCoefficientWeight p (fun k => (v k:ℝ)) j k)*
            (sourceWeightMultiplier j k:ℝ) := by
      rw [sourceCoefficientWeight_multiplier]
      ring
    rw [he]
    have hr' : |(ratSourceRoundedWeight p v B (j+1) k:ℝ)-
        (ratSourceRoundedWeight p v B j k:ℝ)*(sourceWeightMultiplier j k:ℝ)| ≤ 1/(B:ℝ) := by
      simpa only [ratSourceRoundedWeight, Rat.cast_mul] using hr
    calc
      _ ≤ 1/(B:ℝ)+
          |(ratSourceRoundedWeight p v B j k:ℝ)-
            sourceCoefficientWeight p (fun k => (v k:ℝ)) j k| * 2 := by
        apply (abs_add_le _ _).trans
        rw [abs_mul]
        exact add_le_add hr' (mul_le_mul_of_nonneg_left hmabs (abs_nonneg _))
      _ ≤ 1/(B:ℝ)+(((2:ℝ)^(j+1)-1)/(B:ℝ))*2 := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ih (by norm_num : (0:ℝ) ≤ 2))
      _ = ((2:ℝ)^(j+1+1)-1)/(B:ℝ) := by rw [pow_succ]; ring

theorem sourceCoefficientWeight_abs_le (p : ℝ) (v : ℕ → ℝ) (j k : ℕ)
    (hp : 3 ≤ p) (hk : k ≤ 13600) (hv : |v k| ≤ 43046722) :
    |sourceCoefficientWeight p v j k| ≤ 43046722*(2:ℝ)^j := by
  induction j with
  | zero =>
    have hp0 : (0:ℝ) < p := by linarith
    have hnorm : |1/(40*p)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<40*p)).mpr
      linarith
    have hhalf : |(if k=0 then 1/2 else 1:ℝ)| ≤ 1 := by split_ifs <;> norm_num
    rw [sourceCoefficientWeight_zero, abs_mul, abs_mul]
    simpa only [pow_zero, mul_one, one_mul] using
      mul_le_mul (mul_le_mul hnorm hv (abs_nonneg _) (by norm_num))
        hhalf (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1*43046722)
  | succ j ih =>
    rw [sourceCoefficientWeight_multiplier, abs_mul]
    have hm := sourceWeightMultiplier_bounds j k hk
    have hab : |(sourceWeightMultiplier j k:ℝ)| ≤ 2 := by
      rw [abs_of_nonneg hm.1]
      exact hm.2
    calc
      _ ≤ (43046722*(2:ℝ)^j)*2 :=
        mul_le_mul ih hab (abs_nonneg _) (by positivity)
      _ = 43046722*(2:ℝ)^(j+1) := by rw [pow_succ]; ring

def sourceCoefficientScale : ℕ := 10^180

def ratSourceRoundedTrigSeed (q : ℚ) : ℚ × ℚ :=
  (ratRoundLower (ratSourceCosTaylor q) sourceCoefficientScale,
    ratRoundLower (ratSourceSinTaylor q) sourceCoefficientScale)

def ratSourceRoundedTrig (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | k+1 =>
    let r := ratSourceRoundedTrigSeed q
    let w := ratSourceRoundedTrig q k
    (ratRoundLower (w.1*r.1-w.2*r.2) sourceCoefficientScale,
      ratRoundLower (w.2*r.1+w.1*r.2) sourceCoefficientScale)

private theorem sourceCoefficientScale_pos : 0 < sourceCoefficientScale := by
  norm_num [sourceCoefficientScale]

private theorem source_seed_factorial_le_grid :
    1/(Nat.factorial 121:ℝ) ≤ 1/(sourceCoefficientScale:ℝ) := by
  norm_num [sourceCoefficientScale]

theorem ratSourceRoundedTrigSeed_error (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |((ratSourceRoundedTrigSeed q).1:ℝ)-Real.cos (q:ℝ)| ≤
      2/(sourceCoefficientScale:ℝ) ∧
    |((ratSourceRoundedTrigSeed q).2:ℝ)-Real.sin (q:ℝ)| ≤
      2/(sourceCoefficientScale:ℝ) := by
  have hrc := ratRoundLower_error_real (ratSourceCosTaylor q)
    sourceCoefficientScale sourceCoefficientScale_pos
  have hrs := ratRoundLower_error_real (ratSourceSinTaylor q)
    sourceCoefficientScale sourceCoefficientScale_pos
  have hc := ratSourceCosTaylor_error q hq0 hq1
  have hs := ratSourceSinTaylor_error q hq0 hq1
  rw [abs_sub_comm] at hc hs
  constructor
  · have ht := abs_sub_le ((ratSourceRoundedTrigSeed q).1:ℝ)
      (ratSourceCosTaylor q:ℝ) (Real.cos (q:ℝ))
    change |((ratSourceRoundedTrigSeed q).1:ℝ)-(ratSourceCosTaylor q:ℝ)| ≤ _ at hrc
    calc
      _ ≤ 1/(sourceCoefficientScale:ℝ)+1/(sourceCoefficientScale:ℝ) :=
        ht.trans (add_le_add hrc (hc.trans source_seed_factorial_le_grid))
      _ = 2/(sourceCoefficientScale:ℝ) := by ring
  · have ht := abs_sub_le ((ratSourceRoundedTrigSeed q).2:ℝ)
      (ratSourceSinTaylor q:ℝ) (Real.sin (q:ℝ))
    change |((ratSourceRoundedTrigSeed q).2:ℝ)-(ratSourceSinTaylor q:ℝ)| ≤ _ at hrs
    calc
      _ ≤ 1/(sourceCoefficientScale:ℝ)+1/(sourceCoefficientScale:ℝ) :=
        ht.trans (add_le_add hrs (hs.trans source_seed_factorial_le_grid))
      _ = 2/(sourceCoefficientScale:ℝ) := by ring

theorem ratSourceRoundedTrig_step_error (q : ℚ) (j : ℕ) :
    |((ratSourceRoundedTrig q (j+1)).1:ℝ)-
      (((ratSourceRoundedTrig q j).1:ℝ)*((ratSourceRoundedTrigSeed q).1:ℝ)-
        ((ratSourceRoundedTrig q j).2:ℝ)*((ratSourceRoundedTrigSeed q).2:ℝ))| ≤
          1/(sourceCoefficientScale:ℝ) ∧
    |((ratSourceRoundedTrig q (j+1)).2:ℝ)-
      (((ratSourceRoundedTrig q j).2:ℝ)*((ratSourceRoundedTrigSeed q).1:ℝ)+
        ((ratSourceRoundedTrig q j).1:ℝ)*((ratSourceRoundedTrigSeed q).2:ℝ))| ≤
          1/(sourceCoefficientScale:ℝ) := by
  constructor
  · simpa only [ratSourceRoundedTrig, Rat.cast_sub, Rat.cast_mul] using
      ratRoundLower_error_real
        ((ratSourceRoundedTrig q j).1*(ratSourceRoundedTrigSeed q).1-
          (ratSourceRoundedTrig q j).2*(ratSourceRoundedTrigSeed q).2)
        sourceCoefficientScale sourceCoefficientScale_pos
  · simpa only [ratSourceRoundedTrig, Rat.cast_add, Rat.cast_mul] using
      ratRoundLower_error_real
        ((ratSourceRoundedTrig q j).2*(ratSourceRoundedTrigSeed q).1+
          (ratSourceRoundedTrig q j).1*(ratSourceRoundedTrigSeed q).2)
        sourceCoefficientScale sourceCoefficientScale_pos

private theorem sourceTrigGrid_small (k : ℕ) (hk : k ≤ 13600) :
    (k:ℝ)*(2*(1/(sourceCoefficientScale:ℝ))+8*(2/(sourceCoefficientScale:ℝ))) ≤ 1 := by
  have hk' : (k:ℝ) ≤ 13600 := by exact_mod_cast hk
  calc
    _ ≤ 13600*(2*(1/(sourceCoefficientScale:ℝ))+8*(2/(sourceCoefficientScale:ℝ))) := by
      exact mul_le_mul_of_nonneg_right hk' (by positivity)
    _ ≤ 1 := by norm_num [sourceCoefficientScale]

theorem ratSourceRoundedTrig_state_bound (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (k : ℕ) (hk : k ≤ 13600) :
    |((ratSourceRoundedTrig q k).1:ℝ)| ≤ 2 ∧
      |((ratSourceRoundedTrig q k).2:ℝ)| ≤ 2 := by
  have hr := ratSourceRoundedTrigSeed_error q hq0 hq1
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hstate : ∀ j, j < k →
        |((ratSourceRoundedTrig q j).1:ℝ)| ≤ 2 ∧
          |((ratSourceRoundedTrig q j).2:ℝ)| ≤ 2 := by
      intro j hj
      exact ih j hj (by omega)
    have h := sourceTrigRoundedSequence_error (q:ℝ)
      ((ratSourceRoundedTrigSeed q).1:ℝ) ((ratSourceRoundedTrigSeed q).2:ℝ)
      (fun j => ((ratSourceRoundedTrig q j).1:ℝ))
      (fun j => ((ratSourceRoundedTrig q j).2:ℝ))
      (2/(sourceCoefficientScale:ℝ)) (1/(sourceCoefficientScale:ℝ)) k
      (by simp [ratSourceRoundedTrig]) (by simp [ratSourceRoundedTrig])
      hr.1 hr.2 hstate (fun j _ => ratSourceRoundedTrig_step_error q j)
    have hc := abs_le.mp (h.1.trans (sourceTrigGrid_small k hk))
    have hs := abs_le.mp (h.2.trans (sourceTrigGrid_small k hk))
    have hcos := abs_le.mp (Real.abs_cos_le_one ((k:ℝ)*(q:ℝ)))
    have hsin := abs_le.mp (Real.abs_sin_le_one ((k:ℝ)*(q:ℝ)))
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem ratSourceRoundedTrig_error (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (k : ℕ) (hk : k ≤ 13600) :
    |((ratSourceRoundedTrig q k).1:ℝ)-Real.cos ((k:ℝ)*(q:ℝ))| ≤
      18*(k:ℝ)/(sourceCoefficientScale:ℝ) ∧
    |((ratSourceRoundedTrig q k).2:ℝ)-Real.sin ((k:ℝ)*(q:ℝ))| ≤
      18*(k:ℝ)/(sourceCoefficientScale:ℝ) := by
  have hr := ratSourceRoundedTrigSeed_error q hq0 hq1
  have h := sourceTrigRoundedSequence_error (q:ℝ)
    ((ratSourceRoundedTrigSeed q).1:ℝ) ((ratSourceRoundedTrigSeed q).2:ℝ)
    (fun j => ((ratSourceRoundedTrig q j).1:ℝ))
    (fun j => ((ratSourceRoundedTrig q j).2:ℝ))
    (2/(sourceCoefficientScale:ℝ)) (1/(sourceCoefficientScale:ℝ)) k
    (by simp [ratSourceRoundedTrig]) (by simp [ratSourceRoundedTrig]) hr.1 hr.2
    (fun j hj => ratSourceRoundedTrig_state_bound q hq0 hq1 j (by omega))
    (fun j _ => ratSourceRoundedTrig_step_error q j)
  have he : (k:ℝ)*(2*(1/(sourceCoefficientScale:ℝ))+8*(2/(sourceCoefficientScale:ℝ))) =
      18*(k:ℝ)/(sourceCoefficientScale:ℝ) := by ring
  rw [he] at h
  exact h

def ratSourceRoundedTrigFactor (q : ℚ) (j k : ℕ) : ℚ :=
  (if j%4=1 ∨ j%4=2 then -1 else 1) *
    (if j%2=0 then (ratSourceRoundedTrig q k).1 else (ratSourceRoundedTrig q k).2)

theorem ratSourceRoundedTrigFactor_bounds (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (j k : ℕ) (hk : k ≤ 13600) :
    |(ratSourceRoundedTrigFactor q j k:ℝ)| ≤ 2 ∧
      |(ratSourceRoundedTrigFactor q j k:ℝ)-
        sourceTrigFactor j ((k:ℝ)*(q:ℝ))| ≤ 18*(k:ℝ)/(sourceCoefficientScale:ℝ) := by
  have hb := ratSourceRoundedTrig_state_bound q hq0 hq1 k hk
  have he := ratSourceRoundedTrig_error q hq0 hq1 k hk
  by_cases hj4 : j%4=1 ∨ j%4=2 <;> by_cases hj2 : j%2=0
  · simpa [ratSourceRoundedTrigFactor, sourceTrigFactor, hj4, hj2, neg_add_eq_sub, abs_sub_comm] using And.intro hb.1 he.1
  · simpa [ratSourceRoundedTrigFactor, sourceTrigFactor, hj4, hj2, neg_add_eq_sub, abs_sub_comm] using And.intro hb.2 he.2
  · simpa [ratSourceRoundedTrigFactor, sourceTrigFactor, hj4, hj2] using And.intro hb.1 he.1
  · simpa [ratSourceRoundedTrigFactor, sourceTrigFactor, hj4, hj2] using And.intro hb.2 he.2

def ratSourceRoundedCoefficient (c p : ℚ) (v : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 13601,
    ratRoundLower (ratSourceRoundedWeight p v sourceCoefficientScale j k *
      ratSourceRoundedTrigFactor (c/40) j k) sourceCoefficientScale

def sourceRoundedCoefficientTermBudget : ℝ :=
  1/(sourceCoefficientScale:ℝ) + 2*((2:ℝ)^65/(sourceCoefficientScale:ℝ)) +
    (43046722*(2:ℝ)^64)*(18*13600/(sourceCoefficientScale:ℝ))

theorem ratSourceRoundedCoefficient_term_error (q p : ℚ) (v : ℕ → ℚ)
    (j k : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp : 3 ≤ p)
    (hj : j ≤ 64) (hk : k ≤ 13600) (hv : |(v k:ℝ)| ≤ 43046722) :
    |(ratRoundLower (ratSourceRoundedWeight p v sourceCoefficientScale j k *
        ratSourceRoundedTrigFactor q j k) sourceCoefficientScale:ℝ)-
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k *
        sourceTrigFactor j ((k:ℝ)*(q:ℝ))| ≤ sourceRoundedCoefficientTermBudget := by
  have hB : (0:ℝ) < sourceCoefficientScale := by exact_mod_cast sourceCoefficientScale_pos
  have hw := ratSourceRoundedWeight_error p v sourceCoefficientScale j k sourceCoefficientScale_pos hk
  have hw' : |(ratSourceRoundedWeight p v sourceCoefficientScale j k:ℝ)-
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k| ≤
      (2:ℝ)^65/(sourceCoefficientScale:ℝ) := by
    apply hw.trans
    apply (div_le_div_iff_of_pos_right hB).mpr
    have hpow : (2:ℝ)^(j+1) ≤ (2:ℝ)^65 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hp' : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hwa := sourceCoefficientWeight_abs_le (p:ℝ) (fun k => (v k:ℝ)) j k hp' hk hv
  have hwa' : |sourceCoefficientWeight p (fun k => (v k:ℝ)) j k| ≤ 43046722*(2:ℝ)^64 := by
    exact hwa.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by norm_num))
  have ht := ratSourceRoundedTrigFactor_bounds q hq0 hq1 j k hk
  have hte : |(ratSourceRoundedTrigFactor q j k:ℝ)-sourceTrigFactor j ((k:ℝ)*(q:ℝ))| ≤
      18*13600/(sourceCoefficientScale:ℝ) := by
    apply ht.2.trans
    apply (div_le_div_iff_of_pos_right hB).mpr
    have hk' : (k:ℝ) ≤ 13600 := by exact_mod_cast hk
    linarith
  have hr := ratRoundLower_error_real
    (ratSourceRoundedWeight p v sourceCoefficientScale j k * ratSourceRoundedTrigFactor q j k)
    sourceCoefficientScale sourceCoefficientScale_pos
  rw [Rat.cast_mul] at hr
  have he : (ratSourceRoundedWeight p v sourceCoefficientScale j k:ℝ)*
        (ratSourceRoundedTrigFactor q j k:ℝ) -
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k * sourceTrigFactor j ((k:ℝ)*(q:ℝ)) =
      ((ratSourceRoundedWeight p v sourceCoefficientScale j k:ℝ)-
        sourceCoefficientWeight p (fun k => (v k:ℝ)) j k) * (ratSourceRoundedTrigFactor q j k:ℝ) +
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k *
        ((ratSourceRoundedTrigFactor q j k:ℝ)-sourceTrigFactor j ((k:ℝ)*(q:ℝ))) := by ring
  have hprod : |(ratSourceRoundedWeight p v sourceCoefficientScale j k:ℝ)*
        (ratSourceRoundedTrigFactor q j k:ℝ) -
      sourceCoefficientWeight p (fun k => (v k:ℝ)) j k * sourceTrigFactor j ((k:ℝ)*(q:ℝ))| ≤
      ((2:ℝ)^65/(sourceCoefficientScale:ℝ))*2 +
        (43046722*(2:ℝ)^64)*(18*13600/(sourceCoefficientScale:ℝ)) := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul hw' ht.1 (abs_nonneg _) (by positivity))
      (mul_le_mul hwa' hte (abs_nonneg _) (by positivity))
  apply (abs_sub_le _ ((ratSourceRoundedWeight p v sourceCoefficientScale j k:ℝ)*
    (ratSourceRoundedTrigFactor q j k:ℝ)) _).trans
  have h := add_le_add hr hprod
  simpa only [sourceRoundedCoefficientTermBudget, mul_comm ((2:ℝ)^65/(sourceCoefficientScale:ℝ)) 2, add_assoc] using h

theorem sourceRoundedCoefficientBudget_le :
    (13601:ℝ)*sourceRoundedCoefficientTermBudget ≤ 1/(10:ℝ)^125 := by
  norm_num [sourceRoundedCoefficientTermBudget, sourceCoefficientScale]

theorem sourceRoundedCoefficientBudget_lt :
    (13601:ℝ)*sourceRoundedCoefficientTermBudget < 1/(10:ℝ)^140 := by
  norm_num [sourceRoundedCoefficientTermBudget, sourceCoefficientScale]

theorem ratSourceRoundedCoefficient_error_budget (c p : ℚ) (v : ℕ → ℚ) (j : ℕ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 40) (hp : 3 ≤ p) (hj : j ≤ 64)
    (hv : ∀ k, k ≤ 13600 → |(v k:ℝ)| ≤ 43046722) :
    |(ratSourceRoundedCoefficient c p v j:ℝ)-
      (realSampledTaylorPolynomial (c:ℝ) (p:ℝ) (fun k => (v k:ℝ))).coeff j| ≤
        (13601:ℝ)*sourceRoundedCoefficientTermBudget := by
  have hq0 : (0:ℚ) ≤ c/40 := div_nonneg hc0 (by norm_num)
  have hq1 : c/40 ≤ (1:ℚ) := (div_le_iff₀ (by norm_num : (0:ℚ)<40)).mpr (by linarith)
  rw [realSampledTaylorPolynomial_source_coeff _ _ _ _ hj]
  unfold ratSourceRoundedCoefficient
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range 13601, sourceRoundedCoefficientTermBudget := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ 13600 := by have := Finset.mem_range.mp hk; omega
      have ht := ratSourceRoundedCoefficient_term_error (c/40) p v j k hq0 hq1 hp hj hk' (hv k hk')
      simpa only [Rat.cast_div, Rat.cast_ofNat, mul_div_assoc] using ht
    _ = (13601:ℝ)*sourceRoundedCoefficientTermBudget := by simp

theorem ratSourceRoundedCoefficient_error (c p : ℚ) (v : ℕ → ℚ) (j : ℕ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 40) (hp : 3 ≤ p) (hj : j ≤ 64)
    (hv : ∀ k, k ≤ 13600 → |(v k:ℝ)| ≤ 43046722) :
    |(ratSourceRoundedCoefficient c p v j:ℝ)-
      (realSampledTaylorPolynomial (c:ℝ) (p:ℝ) (fun k => (v k:ℝ))).coeff j| ≤
        1/(10:ℝ)^125 :=
  (ratSourceRoundedCoefficient_error_budget c p v j hc0 hc1 hp hj hv).trans
    sourceRoundedCoefficientBudget_le

end ReciprocalXi


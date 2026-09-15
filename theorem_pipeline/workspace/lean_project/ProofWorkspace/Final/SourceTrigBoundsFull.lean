import ProofWorkspace.Final.SourceCoefficientFormulaFull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def ratSourceCosTaylor (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 61, (-1:ℚ)^j*q^(2*j)/(2*j).factorial

def ratSourceSinTaylor (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 61, (-1:ℚ)^j*q^(2*j+1)/(2*j+1).factorial

private theorem seed_power_factorial_antitone (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x^n/(n.factorial:ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : x^(n+1) ≤ x^n := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 n)).trans_eq (mul_one _)
  calc
    x^(n+1)/((n+1).factorial:ℝ) ≤ x^n/((n+1).factorial:ℝ) := by
      exact div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)
    _ ≤ x^n/(n.factorial:ℝ) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hx0 n) (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)

private theorem seed_power_factorial_le_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 121 ≤ n) : x^n/(n.factorial:ℝ) ≤ 1/(Nat.factorial 121:ℝ) := by
  calc
    x^n/(n.factorial:ℝ) ≤ 1/(n.factorial:ℝ) :=
      div_le_div_of_nonneg_right (pow_le_one₀ hx0 hx1) (Nat.cast_nonneg _)
    _ ≤ 1/(Nat.factorial 121:ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.factorial_le hn

theorem ratSourceCosTaylor_error (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |Real.cos (q:ℝ)-(ratSourceCosTaylor q:ℝ)| ≤ 1/(Nat.factorial 121:ℝ) := by
  have hx0 : (0:ℝ) ≤ q := by exact_mod_cast hq0
  have hx1 : (q:ℝ) ≤ 1 := by exact_mod_cast hq1
  have hi : Function.Injective (fun n : ℕ => 2*n) := by
    intro a b hab
    change 2*a=2*b at hab
    omega
  have hm : Monotone (fun n : ℕ => 2*n) := by
    intro a b hab
    change 2*a ≤ 2*b
    omega
  have ha := (seed_power_factorial_antitone q hx0 hx1).comp_monotone hm
  have hs := (Real.summable_pow_div_factorial (q:ℝ)).comp_injective hi
  have hsum : HasSum (fun j : ℕ => (-1:ℝ)^j*((q:ℝ)^(2*j)/(2*j).factorial))
      (Real.cos (q:ℝ)) := by
    simpa only [mul_div_assoc] using Real.hasSum_cos (q:ℝ)
  have h := alternating_series_error_bound
    (fun j : ℕ => (q:ℝ)^(2*j)/(2*j).factorial) ha hs 61
  rw [hsum.tsum_eq] at h
  have hb := seed_power_factorial_le_error q hx0 hx1 (2*61) (by norm_num)
  have ht := h.trans hb
  simpa [ratSourceCosTaylor, mul_div_assoc] using ht

theorem ratSourceSinTaylor_error (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |Real.sin (q:ℝ)-(ratSourceSinTaylor q:ℝ)| ≤ 1/(Nat.factorial 121:ℝ) := by
  have hx0 : (0:ℝ) ≤ q := by exact_mod_cast hq0
  have hx1 : (q:ℝ) ≤ 1 := by exact_mod_cast hq1
  have hi : Function.Injective (fun n : ℕ => 2*n+1) := by
    intro a b hab
    change 2*a+1=2*b+1 at hab
    omega
  have hm : Monotone (fun n : ℕ => 2*n+1) := by
    intro a b hab
    change 2*a+1 ≤ 2*b+1
    omega
  have ha := (seed_power_factorial_antitone q hx0 hx1).comp_monotone hm
  have hs := (Real.summable_pow_div_factorial (q:ℝ)).comp_injective hi
  have hsum : HasSum (fun j : ℕ => (-1:ℝ)^j*((q:ℝ)^(2*j+1)/(2*j+1).factorial))
      (Real.sin (q:ℝ)) := by
    simpa only [mul_div_assoc] using Real.hasSum_sin (q:ℝ)
  have h := alternating_series_error_bound
    (fun j : ℕ => (q:ℝ)^(2*j+1)/(2*j+1).factorial) ha hs 61
  rw [hsum.tsum_eq] at h
  have hb := seed_power_factorial_le_error q hx0 hx1 (2*61+1) (by norm_num)
  have ht := h.trans hb
  simpa [ratSourceSinTaylor, mul_div_assoc] using ht

def sourceRotation (θ : ℝ) : ℂ := (Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I

theorem sourceRotation_norm (θ : ℝ) : ‖sourceRotation θ‖ = 1 := by
  simpa only [sourceRotation, Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.norm_cos_add_sin_mul_I θ

theorem sourceRotation_pow (θ : ℝ) (k : ℕ) :
    sourceRotation θ ^ k = sourceRotation ((k:ℝ)*θ) := by
  induction k with
  | zero => simp [sourceRotation]
  | succ k ih =>
    rw [pow_succ, ih]
    apply Complex.ext <;>
      simp [sourceRotation, Nat.cast_add, Nat.cast_one, add_mul, Real.cos_add,
        Real.sin_add, Complex.mul_re, Complex.mul_im] <;> ring

theorem sourceRotation_accumulated_error (θ : ℝ) (w : ℕ → ℂ) (e : ℕ → ℝ)
    (k : ℕ) (hw0 : w 0 = 1)
    (hstep : ∀ j, j < k → ‖w (j+1)-w j*sourceRotation θ‖ ≤ e j) :
    ‖w k-sourceRotation ((k:ℝ)*θ)‖ ≤ ∑ j ∈ Finset.range k, e j := by
  rw [← sourceRotation_pow]
  revert hstep
  induction k with
  | zero => intro hstep; simp [hw0]
  | succ k ih =>
    intro hstep
    have ih' := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    rw [pow_succ, Finset.sum_range_succ]
    have he : w (k+1)-sourceRotation θ^k*sourceRotation θ =
        (w (k+1)-w k*sourceRotation θ)+(w k-sourceRotation θ^k)*sourceRotation θ := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul, sourceRotation_norm, mul_one]
    exact (add_le_add (hstep k (Nat.lt_succ_self k)) ih').trans_eq (add_comm _ _)

theorem sourceRotation_rounded_error (θ : ℝ) (r : ℂ) (w : ℕ → ℂ)
    (η ε M : ℝ) (k : ℕ) (hw0 : w 0 = 1)
    (hr : ‖r-sourceRotation θ‖ ≤ η) (hw : ∀ j, j < k → ‖w j‖ ≤ M)
    (hstep : ∀ j, j < k → ‖w (j+1)-w j*r‖ ≤ ε) :
    ‖w k-sourceRotation ((k:ℝ)*θ)‖ ≤ (k:ℝ)*(ε+M*η) := by
  have he : ∀ j, j < k → ‖w (j+1)-w j*sourceRotation θ‖ ≤ ε+M*η := by
    intro j hj
    have hd : w (j+1)-w j*sourceRotation θ =
        (w (j+1)-w j*r)+w j*(r-sourceRotation θ) := by ring
    rw [hd]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (hstep j hj)
      (mul_le_mul (hw j hj) hr (norm_nonneg _) ((norm_nonneg _).trans (hw j hj)))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    sourceRotation_accumulated_error θ w (fun _ => ε+M*η) k hw0 he

theorem sourceTrigRoundedSequence_error (θ rc rs : ℝ) (cv sv : ℕ → ℝ)
    (η ρ : ℝ) (k : ℕ) (hc0 : cv 0 = 1) (hs0 : sv 0 = 0)
    (hrc : |rc-Real.cos θ| ≤ η) (hrs : |rs-Real.sin θ| ≤ η)
    (hstate : ∀ j, j < k → |cv j| ≤ 2 ∧ |sv j| ≤ 2)
    (hstep : ∀ j, j < k →
      |cv (j+1)-(cv j*rc-sv j*rs)| ≤ ρ ∧
      |sv (j+1)-(sv j*rc+cv j*rs)| ≤ ρ) :
    |cv k-Real.cos ((k:ℝ)*θ)| ≤ (k:ℝ)*(2*ρ+8*η) ∧
    |sv k-Real.sin ((k:ℝ)*θ)| ≤ (k:ℝ)*(2*ρ+8*η) := by
  let r : ℂ := (rc:ℂ)+(rs:ℂ)*Complex.I
  let w : ℕ → ℂ := fun j => (cv j:ℂ)+(sv j:ℂ)*Complex.I
  have hw0 : w 0 = 1 := by simp [w, hc0, hs0]
  have hr : ‖r-sourceRotation θ‖ ≤ 2*η := by
    have h := Complex.norm_le_abs_re_add_abs_im (r-sourceRotation θ)
    simp only [r, sourceRotation, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
      zero_add, mul_one] at h
    dsimp only [r, sourceRotation]
    linarith
  have hw : ∀ j, j < k → ‖w j‖ ≤ 4 := by
    intro j hj
    have h := Complex.norm_le_abs_re_add_abs_im (w j)
    simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add, mul_one] at h
    obtain ⟨hc, hs⟩ := hstate j hj
    linarith
  have hstep' : ∀ j, j < k → ‖w (j+1)-w j*r‖ ≤ 2*ρ := by
    intro j hj
    have h := Complex.norm_le_abs_re_add_abs_im (w (j+1)-w j*r)
    simp only [w, r, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, mul_one] at h
    obtain ⟨hc, hs⟩ := hstep j hj
    have hs' : |sv (j+1)-(cv j*rs+sv j*rc)| ≤ ρ := by
      simpa only [add_comm] using hs
    linarith
  have h := sourceRotation_rounded_error θ r w (2*η) (2*ρ) 4 k hw0 hr hw hstep'
  have hb : ‖w k-sourceRotation ((k:ℝ)*θ)‖ ≤ (k:ℝ)*(2*ρ+8*η) := by
    convert h using 1
    ring
  have hc := (Complex.abs_re_le_norm (w k-sourceRotation ((k:ℝ)*θ))).trans hb
  have hs := (Complex.abs_im_le_norm (w k-sourceRotation ((k:ℝ)*θ))).trans hb
  simp only [w, sourceRotation, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    zero_add, mul_one] at hc hs
  exact ⟨hc, hs⟩

theorem ratSourceRotation_error (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖(ratSourceCosTaylor q:ℂ)+(ratSourceSinTaylor q:ℂ)*Complex.I-sourceRotation q‖ ≤
      2/(Nat.factorial 121:ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im
    ((ratSourceCosTaylor q:ℂ)+(ratSourceSinTaylor q:ℂ)*Complex.I-sourceRotation q)
  simp only [sourceRotation, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
    Complex.add_im, Complex.mul_im, zero_add, mul_one] at h
  have hc := ratSourceCosTaylor_error q hq0 hq1
  have hs := ratSourceSinTaylor_error q hq0 hq1
  rw [abs_sub_comm] at hc hs
  dsimp only [sourceRotation]
  linarith

end ReciprocalXi

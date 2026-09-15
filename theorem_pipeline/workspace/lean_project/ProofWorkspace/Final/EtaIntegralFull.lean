import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual real eta integral

Existence and normalized Laplace identities hold for all positive real
parameters. The zeta identity here is proved in the absolutely convergent
range s > 1; analytic continuation is not assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace ReciprocalXi

def etaIntegrand (s t : ℝ) : ℝ :=
  t ^ (s - 1) * Real.exp (-t) / (1 + Real.exp (-t))

def etaIntegral (s : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), etaIntegrand s t) / Real.Gamma s

theorem integrableOn_etaIntegrand (s : ℝ) (hs : 0 < s) :
    IntegrableOn (etaIntegrand s) (Ioi 0) := by
  have hg := Real.GammaIntegral_convergent hs
  have hm : AEStronglyMeasurable (etaIntegrand s) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold etaIntegrand
    fun_prop (disch := first | exact Or.inl (ne_of_gt ht) | positivity)
  apply hg.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htn : 0 ≤ t ^ (s - 1) := Real.rpow_nonneg ht.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold etaIntegrand; positivity)]
  unfold etaIntegrand
  calc
    _ ≤ t ^ (s - 1) * Real.exp (-t) :=
      div_le_self (by positivity) (by linarith [Real.exp_pos (-t)])
    _ = _ := mul_comm _ _

theorem etaLaplaceIntegral (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * Real.exp (-(r * t))) =
      Real.Gamma s / r ^ s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr,
    Real.div_rpow (by norm_num) hr.le, Real.one_rpow]
  ring

theorem integrableOn_etaLaplace (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have hg := Real.GammaIntegral_convergent hs
  rw [← mul_zero r, ← integrableOn_Ioi_comp_mul_left_iff _ _ hr] at hg
  have hc := hg.const_mul (1 / r ^ (s - 1))
  apply IntegrableOn.congr_fun hc _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.mul_rpow hr.le ht.le]
  have hn : r ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
  field_simp

theorem etaLaplaceIntegral_normalized (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * Real.exp (-(r * t))) / Real.Gamma s =
      1 / r ^ s := by
  rw [etaLaplaceIntegral s r hs hr]
  have hn : Real.Gamma s ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hs)
  field_simp

theorem etaLaplaceIntegral_nat (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * Real.exp (-(((n : ℝ) + 1) * t))) /
      Real.Gamma s = 1 / ((n : ℝ) + 1) ^ s :=
  etaLaplaceIntegral_normalized s ((n : ℝ) + 1) hs (by positivity)

theorem hasSum_etaIntegrand_laplace (s t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n *
      (t ^ (s - 1) * Real.exp (-(((n : ℝ) + 1) * t)))) (etaIntegrand s t) := by
  have he : Real.exp (-t) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht)
  have hg := (hasSum_geometric_of_norm_lt_one
    (show ‖-Real.exp (-t)‖ < 1 by simpa using he)).mul_left
      (t ^ (s - 1) * Real.exp (-t))
  convert hg using 1
  · funext n
    rw [neg_eq_neg_one_mul (Real.exp (-t)), mul_pow, ← Real.exp_nat_mul]
    have hexp : Real.exp (-(((n : ℝ) + 1) * t)) =
        Real.exp (-t) * Real.exp ((n : ℝ) * -t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  · unfold etaIntegrand
    ring

theorem hasSum_etaIntegral (s : ℝ) (hs : 1 < s) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ s) (etaIntegral s) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  let f : ℕ → ℝ → ℝ := fun n t => (-1 : ℝ) ^ n *
    (t ^ (s - 1) * Real.exp (-(((n : ℝ) + 1) * t)))
  have hi (n : ℕ) : IntegrableOn (f n) (Ioi 0) :=
    (integrableOn_etaLaplace s ((n : ℝ) + 1) hs0 (by positivity)).const_mul _
  have hn (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖f n t‖) =
      Real.Gamma s / ((n : ℝ) + 1) ^ s := by
    rw [← etaLaplaceIntegral s ((n : ℝ) + 1) hs0 (by positivity)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [f]
    rw [abs_mul, abs_pow]
    norm_num only [abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖f n t‖) := by
    simp_rw [hn]
    simpa only [mul_one_div] using hp.mul_left (Real.Gamma s)
  have h := (hasSum_integral_of_summable_integral_norm hi hsum).div_const (Real.Gamma s)
  convert h using 1
  · funext n
    dsimp [f]
    rw [integral_const_mul, etaLaplaceIntegral s ((n : ℝ) + 1) hs0 (by positivity)]
    have hG : Real.Gamma s ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hs0)
    field_simp
  · unfold etaIntegral
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact (hasSum_etaIntegrand_laplace s t ht).tsum_eq.symm

theorem riemannZeta_re_eq_tsum_rpow (s : ℝ) (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have hc := Complex.ofRealCLM.hasSum hp.hasSum
  have hc' : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (s : ℂ))
      ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) := by
    convert hc using 1
    funext n
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + 1),
      Complex.ofReal_add, Complex.ofReal_natCast]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), hc'.tsum_eq]
  rfl

theorem etaIntegral_eq_riemannZeta (s : ℝ) (hs : 1 < s) :
    etaIntegral s = (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ s
  have hf : Summable f := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have he : Summable (fun n : ℕ => f (2 * n)) :=
    hf.comp_injective (by intro a b h; omega)
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hf.comp_injective (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hsplit := tsum_even_add_odd he ho
  have hodd : (∑' n : ℕ, f (2 * n + 1)) =
      (1 / (2 : ℝ) ^ s) * ∑' n : ℕ, f n := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    dsimp [f]
    push_cast
    rw [show (2 : ℝ) * n + 1 + 1 = 2 * ((n : ℝ) + 1) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    ring
  have halt : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n)
      ((∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1)) := by
    apply HasSum.even_add_odd
    · simpa [pow_mul] using he.hasSum
    · simpa [pow_add, pow_mul] using ho.hasSum.neg
  have het : (∑' n : ℕ, f (2 * n)) - (∑' n : ℕ, f (2 * n + 1)) = etaIntegral s := by
    apply halt.unique
    simpa only [f, mul_one_div] using hasSum_etaIntegral s hs
  have hp : (2 : ℝ) ^ (1 - s) = 2 * (1 / (2 : ℝ) ^ s) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_neg (by norm_num), one_div]
  rw [hp, riemannZeta_re_eq_tsum_rpow s hs]
  change etaIntegral s = (1 - 2 * (1 / (2 : ℝ) ^ s)) * ∑' n : ℕ, f n
  nlinarith

end ReciprocalXi

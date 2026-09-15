import ProofWorkspace.Final.EtaIntegralFull
import ProofWorkspace.Final.XiDefinitionFull
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Actual eta continuation

The defining Mellin integral is holomorphic on Re(s)>0. The regularized Xi
identity follows by the identity principle and gives the actual zeta formula
throughout that half-plane away from s=1, with no assumed continuation.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace ReciprocalXi

def etaKernel (t : ℝ) : ℂ := (Real.exp (-t) / (1 + Real.exp (-t)) : ℝ)

def complexEtaIntegral (s : ℂ) : ℂ := mellin etaKernel s / Complex.Gamma s

theorem continuous_etaKernel : Continuous etaKernel := by
  unfold etaKernel
  apply Complex.continuous_ofReal.comp
  exact (Real.continuous_exp.comp continuous_id.neg).div
    (continuous_const.add (Real.continuous_exp.comp continuous_id.neg))
    (fun t => ne_of_gt (by positivity))

theorem etaKernel_norm_le_exp (t : ℝ) : ‖etaKernel t‖ ≤ Real.exp (-t) := by
  rw [etaKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (Real.exp_pos _).le (by linarith [Real.exp_pos (-t)])

theorem etaKernel_norm_le_one (t : ℝ) : ‖etaKernel t‖ ≤ 1 := by
  rw [etaKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem etaKernel_isBigO_exp : etaKernel =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
  apply IsBigO.of_bound 1
  filter_upwards with t
  simpa using etaKernel_norm_le_exp t

theorem etaKernel_isBigO_zero : etaKernel =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards with t
  simpa using etaKernel_norm_le_one t

theorem mellinConvergent_etaKernel (s : ℂ) (hs : 0 < s.re) : MellinConvergent etaKernel s :=
  mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1)
    (continuous_etaKernel.continuousOn.locallyIntegrableOn measurableSet_Ioi) etaKernel_isBigO_exp
    etaKernel_isBigO_zero hs

theorem differentiableAt_complexEtaIntegral (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ complexEtaIntegral s := by
  unfold complexEtaIntegral
  simp_rw [div_eq_mul_inv]
  exact (mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1)
    (continuous_etaKernel.continuousOn.locallyIntegrableOn measurableSet_Ioi) etaKernel_isBigO_exp
    etaKernel_isBigO_zero hs).mul (Complex.differentiable_one_div_Gamma s)

theorem complexEtaIntegral_ofReal (s : ℝ) :
    complexEtaIntegral (s : ℂ) = (etaIntegral s : ℂ) := by
  rw [complexEtaIntegral, Complex.Gamma_ofReal, etaIntegral, Complex.ofReal_div]
  congr 1
  rw [mellin, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul, etaKernel, etaIntegrand]
  have hpow : (t : ℂ) ^ ((s : ℂ) - 1) = ((t ^ (s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hpow]
  push_cast
  ring

theorem riemannZeta_ofReal_eq_re_of_one_lt (s : ℝ) (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  rw [riemannZeta_re_eq_tsum_rpow s hs,
    zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  have hc := (Complex.ofRealCLM.hasSum hp.hasSum).tsum_eq
  convert hc using 1
  congr 1
  funext n
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + 1),
    Complex.ofReal_add, Complex.ofReal_natCast]

def etaRegularizedXi (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * 2 * xi s / (s * Complex.Gammaℝ s)

theorem complexEtaIntegral_regularized_ofReal (s : ℝ) (hs : 1 < s) :
    ((s : ℂ) - 1) * complexEtaIntegral (s : ℂ) = etaRegularizedXi (s : ℂ) := by
  rw [complexEtaIntegral_ofReal, etaIntegral_eq_riemannZeta s hs,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
    Complex.ofReal_sub, Complex.ofReal_one,
    ← riemannZeta_ofReal_eq_re_of_one_lt s hs]
  have h0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h1 : (s : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hs
  rw [etaRegularizedXi, xi_eq_completed _ h0 h1, riemannZeta_def_of_ne_zero h0]
  norm_num only [Complex.ofReal_ofNat]
  have hG : Complex.Gammaℝ (s : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using lt_trans zero_lt_one hs)
  field_simp

theorem differentiableAt_etaRegularizedXi (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ etaRegularizedXi s := by
  have h0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) s := by
    fun_prop
  unfold etaRegularizedXi
  simp only [div_eq_mul_inv, mul_inv_rev]
  exact ((((differentiableAt_const 1).sub hpow).mul_const 2).mul
    (differentiable_xi s)).mul
    ((Complex.differentiable_Gammaℝ_inv s).mul (differentiableAt_id.inv h0))

theorem complexEtaIntegral_regularized (s : ℂ) (hs : 0 < s.re) :
    (s - 1) * complexEtaIntegral s = etaRegularizedXi s := by
  let U : Set ℂ := {s | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hleft : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * complexEtaIntegral s) U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_complexEtaIntegral z hz)).differentiableWithinAt
  have hright : AnalyticOnNhd ℂ etaRegularizedXi U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    exact (differentiableAt_etaRegularizedXi z hz).differentiableWithinAt
  have hlim : Tendsto (fun n : ℕ => ((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (2 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hr := (tendsto_const_nhds (x := (2 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
      simpa only [Function.comp_apply, add_zero] using hc
    · filter_upwards with n
      simp only [mem_compl_iff, mem_singleton_iff]
      have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
      intro h
      have hh := congrArg Complex.re h
      change 2 + 1 / ((n : ℝ) + 1) = 2 at hh
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), (z - 1) * complexEtaIntegral z = etaRegularizedXi z :=
    hlim.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n =>
      complexEtaIntegral_regularized_ofReal (2 + 1 / ((n : ℝ) + 1))
        (by
          have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith))))
  exact hleft.eqOn_of_preconnected_of_frequently_eq hright
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num [U]) hfreq hs

theorem complexEtaIntegral_eq_riemannZeta (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    complexEtaIntegral s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hsm : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have he := complexEtaIntegral_regularized s hs
  rw [etaRegularizedXi, xi_eq_completed s h0 hs1] at he
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp at he ⊢
  linear_combination he

theorem etaIntegral_eq_riemannZeta_of_pos (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    etaIntegral s = (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re := by
  have he := complexEtaIntegral_eq_riemannZeta (s : ℂ) (by simpa using hs)
    (by exact_mod_cast hs1)
  rw [complexEtaIntegral_ofReal] at he
  have hpow : (2 : ℂ) ^ (1 - (s : ℂ)) = ((2 : ℝ) ^ (1 - s) : ℝ) := by
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hpow] at he
  have hre := congrArg Complex.re he
  simpa [Complex.mul_re] using hre

end ReciprocalXi

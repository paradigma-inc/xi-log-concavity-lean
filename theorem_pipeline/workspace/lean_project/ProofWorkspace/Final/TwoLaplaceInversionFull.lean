import ProofWorkspace.Final.TwoLaplaceFourierFull
import ProofWorkspace.Final.AngularFourierInversionFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

def twoLaplaceMultiplier (a b u : ℝ) : ℂ :=
  ((a:ℂ)^2/((a:ℂ)^2+(u:ℂ)^2))*((b:ℂ)^2/((b:ℂ)^2+(u:ℂ)^2))

theorem integrable_laplace_multiplier {a : ℝ} (ha : 0<a) :
    Integrable (fun u : ℝ ↦ a^2/(a^2+u^2)) := by
  have hh := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero ha.ne')
  apply hh.congr
  filter_upwards with u
  have hd : a^2+u^2≠0 := by nlinarith [sq_nonneg u]
  field_simp

theorem integrable_twoLaplaceMultiplier {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Integrable (twoLaplaceMultiplier a b) := by
  have hreal : Integrable (fun u : ℝ ↦ (a^2/(a^2+u^2))*(b^2/(b^2+u^2))) := by
    apply (integrable_laplace_multiplier ha).mono' (by fun_prop)
    filter_upwards with u
    have hap : 0<a^2+u^2 := by nlinarith [sq_nonneg u]
    have hbp : 0<b^2+u^2 := by nlinarith [sq_nonneg u]
    have hr : b^2/(b^2+u^2)≤1 := (div_le_one hbp).mpr (le_add_of_nonneg_right (sq_nonneg u))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (div_nonneg (sq_nonneg a) hap.le) (div_nonneg (sq_nonneg b) hbp.le))]
    exact mul_le_of_le_one_right (div_nonneg (sq_nonneg a) hap.le) hr
  have hh := Complex.ofRealCLM.integrable_comp hreal
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_pow, twoLaplaceMultiplier] using hh

theorem angularFourier_twoLaplace {a b : ℝ} (ha : 0<a) (hab : a<b) :
    angularFourier (fun x : ℝ ↦ (twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x:ℂ))=
      twoLaplaceMultiplier a b := by
  ext u
  exact integral_twoLaplace_normalized_character ha hab u

theorem angularInverse_twoLaplaceMultiplier {a b : ℝ} (ha : 0<a) (hab : a<b) (x : ℝ) :
    angularInverse (twoLaplaceMultiplier a b) x=
      (twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x:ℂ) := by
  have hc : Continuous (fun x : ℝ ↦ (twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x:ℂ)) := by
    simp_rw [twoLaplaceJet_zero]
    fun_prop
  have hi := Complex.ofRealCLM.integrable_comp
    (integrable_twoLaplace_kernel (a*b/(2*(b^2-a^2))) ha (ha.trans hab))
  have hF : Integrable (angularFourier
      (fun x : ℝ ↦ (twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x:ℂ))) := by
    rw [angularFourier_twoLaplace ha hab]
    exact integrable_twoLaplaceMultiplier ha (ha.trans hab)
  rw [← angularFourier_twoLaplace ha hab]
  exact angularInverse_angularFourier_eq _ hi hF hc.continuousAt

end ReciprocalXi

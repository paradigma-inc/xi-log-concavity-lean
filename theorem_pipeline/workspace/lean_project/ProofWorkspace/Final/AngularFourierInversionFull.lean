import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped FourierTransform
namespace ReciprocalXi

def angularFourier (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, f x*Complex.exp ((u:ℂ)*(x:ℂ)*I)

def angularInverse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∫ u : ℝ, f u*Complex.exp (-I*(x:ℂ)*(u:ℂ)))/(2*(Real.pi:ℂ))

theorem fourier_eq_angularFourier (f : ℝ → ℂ) (u : ℝ) :
    𝓕 f u=angularFourier f (-2*Real.pi*u) := by
  rw [Real.fourier_real_eq_integral_exp_smul, angularFourier]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm (f x)]
  congr 2
  push_cast
  ring

theorem angularInverse_eq_fourierInv (f : ℝ → ℂ) (x : ℝ) :
    angularInverse f x=𝓕⁻ (fun v : ℝ ↦ f (-2*Real.pi*v)) x := by
  have he : (∫ v : ℝ, f (-2*Real.pi*v)*
      Complex.exp (-I*(x:ℂ)*((-2*Real.pi*v:ℝ):ℂ)))=
        angularInverse f x := by
    rw [Measure.integral_comp_mul_left
      (fun u : ℝ ↦ f u*Complex.exp (-I*(x:ℂ)*(u:ℂ))) (-2*Real.pi)]
    rw [abs_inv, abs_mul, abs_of_neg (by norm_num : (-2:ℝ)<0),
      abs_of_pos Real.pi_pos]
    simp only [neg_neg, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat, angularInverse, div_eq_mul_inv]
    ring
  rw [← he, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with v
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm (f _)]
  congr 2
  push_cast
  ring

theorem angularInverse_angularFourier_eq (f : ℝ → ℂ)
    (hi : Integrable f) (hF : Integrable (angularFourier f)) {x : ℝ}
    (hx : ContinuousAt f x) : angularInverse (angularFourier f) x=f x := by
  have hn : (-2*Real.pi:ℝ)≠0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hf : 𝓕 f=(fun u : ℝ ↦ angularFourier f (-2*Real.pi*u)) :=
    funext (fourier_eq_angularFourier f)
  have hiF : Integrable (𝓕 f) := by
    rw [hf]
    exact hF.comp_mul_left' hn
  rw [angularInverse_eq_fourierInv, ← hf]
  exact hi.fourierInv_fourier_eq hiF hx

end ReciprocalXi

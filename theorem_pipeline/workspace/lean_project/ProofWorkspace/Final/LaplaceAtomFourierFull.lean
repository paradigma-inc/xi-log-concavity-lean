import ProofWorkspace.Final.ConvolutionRemainderFull
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

def laplaceAtomCharacter (a u x : ℝ) : ℂ :=
  (Real.exp (-a*|x|):ℂ)*Complex.exp ((u:ℂ)*(x:ℂ)*I)

theorem laplaceAtomCharacter_nonpos (a u x : ℝ) (hx : x≤0) :
    laplaceAtomCharacter a u x=Complex.exp (((a:ℂ)+(u:ℂ)*I)*(x:ℂ)) := by
  rw [laplaceAtomCharacter, Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonpos hx]
  congr 1
  push_cast
  ring

theorem laplaceAtomCharacter_nonneg (a u x : ℝ) (hx : 0≤x) :
    laplaceAtomCharacter a u x=Complex.exp ((-(a:ℂ)+(u:ℂ)*I)*(x:ℂ)) := by
  rw [laplaceAtomCharacter, Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonneg hx]
  congr 1
  push_cast
  ring

theorem integrableOn_laplaceAtomCharacter_Iic {a : ℝ} (ha : 0<a) (u : ℝ) :
    IntegrableOn (laplaceAtomCharacter a u) (Iic 0) := by
  have hh := integrableOn_exp_mul_complex_Iic (a:=(a:ℂ)+(u:ℂ)*I)
    (by simpa using ha) 0
  exact hh.congr_fun (fun x hx ↦ (laplaceAtomCharacter_nonpos a u x hx).symm) measurableSet_Iic

theorem integrableOn_laplaceAtomCharacter_Ioi {a : ℝ} (ha : 0<a) (u : ℝ) :
    IntegrableOn (laplaceAtomCharacter a u) (Ioi 0) := by
  have hh := integrableOn_exp_mul_complex_Ioi (a:=-(a:ℂ)+(u:ℂ)*I)
    (by simpa using neg_neg_of_pos ha) 0
  exact hh.congr_fun (fun x hx ↦ (laplaceAtomCharacter_nonneg a u x hx.le).symm) measurableSet_Ioi

theorem integrable_laplaceAtomCharacter {a : ℝ} (ha : 0<a) (u : ℝ) :
    Integrable (laplaceAtomCharacter a u) := by
  have hh := (integrableOn_laplaceAtomCharacter_Iic ha u).union
    (integrableOn_laplaceAtomCharacter_Ioi ha u)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hh

theorem integral_laplaceAtomCharacter {a : ℝ} (ha : 0<a) (u : ℝ) :
    (∫ x : ℝ, laplaceAtomCharacter a u x)=2*(a:ℂ)/((a:ℂ)^2+(u:ℂ)^2) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_laplaceAtomCharacter_Iic ha u)
    (integrableOn_laplaceAtomCharacter_Ioi ha u)]
  have hl : (∫ x : ℝ in Iic 0, laplaceAtomCharacter a u x)=
      ((a:ℂ)+(u:ℂ)*I)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun x hx ↦ laplaceAtomCharacter_nonpos a u x hx),
      integral_exp_mul_complex_Iic (by simpa using ha)]
    simp
  have hr : (∫ x : ℝ in Ioi 0, laplaceAtomCharacter a u x)=
      -(-(a:ℂ)+(u:ℂ)*I)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ laplaceAtomCharacter_nonneg a u x hx.le),
      integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha)]
    simp [div_eq_mul_inv]
  rw [hl, hr]
  have hn : (a:ℂ)+(u:ℂ)*I≠0 := by
    apply Complex.ne_zero_of_re_pos
    simpa using ha
  have hm : -(a:ℂ)+(u:ℂ)*I≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.zero_re] at hh
    linarith
  have hd : (a:ℂ)^2+(u:ℂ)^2≠0 := by
    have hh : 0<a^2+u^2 := by nlinarith [sq_nonneg u]
    exact_mod_cast hh.ne'
  field_simp
  ring_nf
  simp [I_sq]

end ReciprocalXi

import ProofWorkspace.Final.XiHighZeroBoundFull
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace ReciprocalXi

theorem high_zero_heat_lower {a : ℂ} {c t : ℝ} (ha : 100 ≤ a.re)
    (hi : |a.im| ≤ 1) (hc : 0 ≤ c) (hca : 2*c ≤ a.re) (ht : 0 < t) :
    -Real.exp (-c^2*t)*Real.exp (-a.re/2) ≤ (Complex.exp (-a^2*(t:ℂ))).re := by
  by_cases hn : 0 ≤ (Complex.exp (-a^2*(t:ℂ))).re
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (Real.exp_pos _).le).trans hn
  have hneg : (Complex.exp (-a^2*(t:ℂ))).re < 0 := lt_of_not_ge hn
  have hcos : Real.cos ((-a^2*(t:ℂ)).im) < 0 := by
    rw [Complex.exp_re] at hneg
    by_contra h
    exact not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt h)) hneg
  have hang : Real.pi/2 < |(-a^2*(t:ℂ)).im| := by
    by_contra h
    have hh : |(-a^2*(t:ℂ)).im| ≤ Real.pi/2 := le_of_not_gt h
    exact not_le_of_gt hcos (Real.cos_nonneg_of_mem_Icc (abs_le.mp hh))
  have harg : (-a^2*(t:ℂ)).im = -2*a.re*a.im*t := by
    simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha0 : 0 ≤ a.re := by linarith
  have hangb : |(-a^2*(t:ℂ)).im| ≤ 2*a.re*t := by
    rw [harg, abs_mul, abs_mul, abs_mul]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [abs_of_nonneg ha0, abs_of_pos ht]
    calc
      2*a.re * |a.im| * t ≤ 2*a.re*1*t := by gcongr
      _ = _ := by ring
  have hat : 3/4 ≤ a.re*t := by linarith [Real.pi_gt_three]
  have ha2 : (100:ℝ)^2 ≤ a.re^2 := pow_le_pow_left₀ (by norm_num) ha 2
  have hi2 : a.im^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hi
  have hc2 : (2*c)^2 ≤ a.re^2 := pow_le_pow_left₀ (by positivity) hca 2
  have hd : (2/3)*a.re^2 ≤ (a^2).re-c^2 := by
    simp only [pow_two, Complex.mul_re]
    norm_num at ha2
    nlinarith
  have hdt := mul_le_mul_of_nonneg_right hd ht.le
  have hat' := mul_le_mul_of_nonneg_left hat ha0
  have hexp : c^2*t+a.re/2 ≤ (a^2).re*t := by nlinarith
  have hnorm : ‖Complex.exp (-a^2*(t:ℂ))‖ ≤
      Real.exp (-c^2*t)*Real.exp (-a.re/2) := by
    rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    nlinarith
  have hreal := Complex.re_le_norm (-Complex.exp (-a^2*(t:ℂ)))
  simp only [Complex.neg_re, norm_neg] at hreal
  nlinarith

def F_highHeatTrace (T t : ℝ) : ℂ :=
  ∑' z : FHighZeroOccurrence T, F_zeroHeatTerm z.val t

theorem F_highHeatTrace_lower {T c t : ℝ} (hT : 100 ≤ T)
    (hc : 0 ≤ c) (hTc : 2*c ≤ T) (ht : 0 < t) :
    -(7/100)*Real.exp (-c^2*t) ≤ (F_highHeatTrace T t).re := by
  have hs : Summable (fun z : FHighZeroOccurrence T ↦ F_zeroHeatTerm z.val t) :=
    (summable_F_zeroHeatTerm ht).subtype (fun z ↦ T≤(F_pairRoot z).re)
  have hsre : Summable (fun z : FHighZeroOccurrence T ↦ (F_zeroHeatTerm z.val t).re) :=
    (Complex.reCLM.hasSum hs.hasSum).summable
  have hb := (summable_F_highZero_exp hT).mul_left (-Real.exp (-c^2*t))
  have hp : ∀ z : FHighZeroOccurrence T,
      -Real.exp (-c^2*t)*Real.exp (-(F_pairRoot z.val).re/2) ≤ (F_zeroHeatTerm z.val t).re := by
    intro z
    exact high_zero_heat_lower (hT.trans z.property)
      (F_zero_im_bound _ (F_pairRoot_is_zero z.val)).le hc (hTc.trans z.property) ht
  rw [F_highHeatTrace, Complex.re_tsum hs]
  calc
    _ ≤ -Real.exp (-c^2*t)*(∑' z : FHighZeroOccurrence T,
        Real.exp (-(F_pairRoot z.val).re/2)) := by
      have h := mul_le_mul_of_nonpos_left (F_highZero_exp_tsum_le hT)
        (neg_nonpos.mpr (Real.exp_pos (-c^2*t)).le)
      nlinarith
    _ = ∑' z : FHighZeroOccurrence T,
        -Real.exp (-c^2*t)*Real.exp (-(F_pairRoot z.val).re/2) := tsum_mul_left.symm
    _ ≤ _ := hb.tsum_le_tsum hp hsre

end ReciprocalXi


import ProofWorkspace.Final.XiZeroSymmetryFull
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section
open Set
namespace ReciprocalXi

theorem F_vertical_im_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (F ((x:ℂ)+Complex.I*y)).im)
      (deriv F ((x:ℂ)+Complex.I*t)).re t := by
  have hl : HasDerivAt (fun z : ℂ ↦ (x:ℂ)+Complex.I*z) Complex.I (t:ℂ) := by
    convert ((hasDerivAt_id (t:ℂ)).const_mul Complex.I).const_add (x:ℂ) using 1 <;> simp
  have hf := (differentiable_F_complex ((x:ℂ)+Complex.I*t)).hasDerivAt.comp (t:ℂ) hl
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf.comp_ofReal
  simpa [Complex.mul_im] using hi

theorem F_vertical_im_zero (x : ℝ) : (F ((x:ℂ)+Complex.I*(0:ℝ))).im=0 := by
  have hc := F_conj (x:ℂ)
  rw [Complex.conj_ofReal] at hc
  have hi := congrArg Complex.im hc
  simp at hi ⊢
  linarith

theorem F_vertical_zero_of_deriv_pos (x y : ℝ) (hy : y∈Ioo (-1:ℝ) 1)
    (hp : ∀ t∈Ioo (-1:ℝ) 1, 0<(deriv F ((x:ℂ)+Complex.I*t)).re)
    (hz : F ((x:ℂ)+Complex.I*y)=0) : y=0 := by
  have hm : StrictMonoOn (fun t : ℝ ↦ (F ((x:ℂ)+Complex.I*t)).im) (Ioo (-1:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact fun t _ ↦ (F_vertical_im_hasDerivAt x t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(F_vertical_im_hasDerivAt x t).deriv]
      exact hp t (interior_subset ht)
  apply hm.injOn hy (by norm_num)
  change (F ((x:ℂ)+Complex.I*y)).im=(F ((x:ℂ)+Complex.I*(0:ℝ))).im
  rw [hz,Complex.zero_im,F_vertical_im_zero]

theorem F_vertical_zero_of_deriv_neg (x y : ℝ) (hy : y∈Ioo (-1:ℝ) 1)
    (hp : ∀ t∈Ioo (-1:ℝ) 1, (deriv F ((x:ℂ)+Complex.I*t)).re<0)
    (hz : F ((x:ℂ)+Complex.I*y)=0) : y=0 := by
  have hm : StrictAntiOn (fun t : ℝ ↦ (F ((x:ℂ)+Complex.I*t)).im) (Ioo (-1:ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · exact fun t _ ↦ (F_vertical_im_hasDerivAt x t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(F_vertical_im_hasDerivAt x t).deriv]
      exact hp t (interior_subset ht)
  apply hm.injOn hy (by norm_num)
  change (F ((x:ℂ)+Complex.I*y)).im=(F ((x:ℂ)+Complex.I*(0:ℝ))).im
  rw [hz,Complex.zero_im,F_vertical_im_zero]

theorem F_zero_real_of_vertical_deriv_sign (z : ℂ) (hz : F z=0)
    (hp : (∀ t∈Ioo (-1:ℝ) 1, 0<(deriv F ((z.re:ℂ)+Complex.I*t)).re) ∨
      (∀ t∈Ioo (-1:ℝ) 1, (deriv F ((z.re:ℂ)+Complex.I*t)).re<0)) :
    z.im=0 := by
  have hy := abs_lt.mp (F_zero_im_bound z hz)
  have he : (z.re:ℂ)+Complex.I*z.im=z := by
    apply Complex.ext <;> simp
  have hz' : F ((z.re:ℂ)+Complex.I*z.im)=0 := by rw [he]; exact hz
  rcases hp with hp | hp
  · exact F_vertical_zero_of_deriv_pos z.re z.im hy hp hz'
  · exact F_vertical_zero_of_deriv_neg z.re z.im hy hp hz'

theorem F_zero_simple_of_deriv_re_ne_zero (z : ℂ) (hz : F z=0)
    (hd : (deriv F z).re≠0) : analyticOrderNatAt F z=1 := by
  have hd' : deriv F z≠0 := by
    intro h
    apply hd
    rw [h,Complex.zero_re]
  have ho := (analyticOnNhd_F z (mem_univ z)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd'
  have he : (fun w ↦ F w-F z)=F := by funext w; rw [hz,sub_zero]
  rw [he] at ho
  simp [analyticOrderNatAt,ho]

end ReciprocalXi


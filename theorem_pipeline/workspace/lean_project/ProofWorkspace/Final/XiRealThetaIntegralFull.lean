import ProofWorkspace.Final.XiZeroSymmetryFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Complex
open scoped ComplexConjugate
namespace ReciprocalXi

def realThetaCosineIntegrand (x t : ℝ) : ℝ :=
  t^(-3/4:ℝ)*Real.cos ((x/4)*Real.log t)*(HurwitzZeta.cosKernel 0 t-1)

theorem thetaMellinIntegrand_re_cosine (x t : ℝ) (ht : 0<t) :
    (thetaMellinIntegrand ((1/4:ℂ)+I*(x:ℂ)/4) t).re=realThetaCosineIntegrand x t := by
  have ht0 : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  rw [thetaMellinIntegrand, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le,
    Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, add_zero, zero_add, one_mul]
  unfold realThetaCosineIntegrand
  rw [Real.rpow_def_of_pos ht]
  congr 2 <;> congr 1 <;> ring

theorem integrableOn_realThetaCosineIntegrand (x : ℝ) :
    IntegrableOn (realThetaCosineIntegrand x) (Ioi 1) := by
  have h := Complex.reCLM.integrable_comp
    (integrableOn_thetaMellinIntegrand ((1/4:ℂ)+I*(x:ℂ)/4) (by simp; norm_num))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact thetaMellinIntegrand_re_cosine x t (lt_trans zero_lt_one ht)

theorem F_real_eq_theta_cosine_integral (x : ℝ) :
    (F (x:ℂ)).re=(1-((1+x^2)/4)*∫ t : ℝ in Ioi 1, realThetaCosineIntegrand x t)/8 := by
  let s : ℂ := 1/2+I*(x:ℂ)/2
  let J : ℂ := ∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s/2) t
  have hs : s.re=1/2 := by simp [s]
  have hconj : (1-s)/2=conj (s/2) := by
    dsimp [s]
    simp only [map_div₀, map_sub, map_add, map_mul, map_one, map_ofNat,
      Complex.conj_I, Complex.conj_ofReal]
    ring
  have hc := completedRiemannZeta₀_eq_thetaMellin s (by rw [hs]; norm_num) (by rw [hs]; norm_num)
  rw [hconj, ← thetaMellinIntegral_conj] at hc
  change completedRiemannZeta₀ s=(J+conj J)/2 at hc
  have hp : s*(s-1)=(-((1+x^2)/4):ℝ) := by dsimp [s]; push_cast; ring_nf; simp [I_sq]; ring
  have hj : J.re=∫ t : ℝ in Ioi 1, realThetaCosineIntegrand x t := by
    dsimp [J]
    have hir := Complex.reCLM.integral_comp_comm
      (integrableOn_thetaMellinIntegrand (s/2) (by simp [s]; norm_num))
    change (∫ t : ℝ in Ioi 1, (thetaMellinIntegrand (s/2) t).re)=
      (∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s/2) t).re at hir
    rw [← hir]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have he : s/2=(1/4:ℂ)+I*(x:ℂ)/4 := by dsimp [s]; ring
    rw [he]
    exact thetaMellinIntegrand_re_cosine x t (lt_trans zero_lt_one ht)
  change ((s*(s-1)*completedRiemannZeta₀ s+1)/2/4).re=_
  rw [hp,hc]
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re, Complex.conj_re]
  rw [hj]
  ring

end ReciprocalXi

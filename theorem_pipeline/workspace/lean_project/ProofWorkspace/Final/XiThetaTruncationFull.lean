import ProofWorkspace.Final.XiRealThetaIntegralFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Complex
namespace ReciprocalXi

theorem realThetaCosineIntegrand_abs_le (x t : ℝ) (ht : 1≤t) :
    |realThetaCosineIntegrand x t|≤4*Real.exp (-Real.pi*t) := by
  rw [← thetaMellinIntegrand_re_cosine x t (lt_of_lt_of_le zero_lt_one ht)]
  exact (Complex.abs_re_le_norm _).trans
    (thetaMellinIntegrand_norm_le ((1/4:ℂ)+I*(x:ℂ)/4) (by simp; norm_num) t ht)

theorem realThetaCosineIntegral_tail_abs_le (x T : ℝ) (hT : 1≤T) :
    |∫ t : ℝ in Ioi T, realThetaCosineIntegrand x t|≤4*Real.exp (-Real.pi*T)/Real.pi := by
  have hi := (integrableOn_realThetaCosineIntegrand x).mono_set
    (show Ioi T⊆Ioi (1:ℝ) from fun _ ht ↦ hT.trans_lt ht)
  have hmajor := (exp_neg_integrableOn_Ioi T Real.pi_pos).const_mul 4
  calc
    _ ≤ ∫ t : ℝ in Ioi T, |realThetaCosineIntegrand x t| := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ in Ioi T, 4*Real.exp (-Real.pi*t) := by
      apply integral_mono_ae hi.abs hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact realThetaCosineIntegrand_abs_le x t (hT.trans ht.le)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) T]
      ring

theorem F_real_finite_theta_integral_error (x T : ℝ) (hT : 1≤T) :
    |(F (x:ℂ)).re-(1-((1+x^2)/4)*(∫ t : ℝ in Ioc 1 T, realThetaCosineIntegrand x t))/8|≤
      (1+x^2)*Real.exp (-Real.pi*T)/(8*Real.pi) := by
  have hi := integrableOn_realThetaCosineIntegrand x
  have hs : Ioi (1:ℝ)=Ioc 1 T∪Ioi T := (Ioc_union_Ioi_eq_Ioi hT).symm
  have hd : Disjoint (Ioc (1:ℝ) T) (Ioi T) := by
    apply Set.disjoint_left.mpr
    intro t h1 h2
    exact not_lt_of_ge h1.2 h2
  have hsplit : (∫ t : ℝ in Ioi 1, realThetaCosineIntegrand x t)=
      (∫ t : ℝ in Ioc 1 T, realThetaCosineIntegrand x t)+
      (∫ t : ℝ in Ioi T, realThetaCosineIntegrand x t) := by
    rw [hs]
    exact setIntegral_union hd measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self)
      (hi.mono_set (show Ioi T⊆Ioi (1:ℝ) from fun _ ht ↦ hT.trans_lt ht))
  have he := realThetaCosineIntegral_tail_abs_le x T hT
  rw [F_real_eq_theta_cosine_integral, hsplit]
  have hid (A B : ℝ) :
      (1-((1+x^2)/4)*(A+B))/8-(1-((1+x^2)/4)*A)/8=-((1+x^2)/32)*B := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0≤(1+x^2)/32)]
  calc
    _ ≤ ((1+x^2)/32)*(4*Real.exp (-Real.pi*T)/Real.pi) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end ReciprocalXi


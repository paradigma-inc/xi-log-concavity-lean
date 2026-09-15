import ProofWorkspace.Final.XiThetaFiniteSumFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

theorem continuousOn_realThetaFiniteIntegrand (x : ℝ) (N : ℕ) :
    ContinuousOn (realThetaFiniteIntegrand x N) (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have ht0 : t≠0 := ne_of_gt ht
  have hp : ContinuousAt (fun y : ℝ ↦ y^(-3/4:ℝ)) t :=
    continuousAt_id.rpow_const (Or.inl ht0)
  have hl0 : ContinuousAt (fun y : ℝ ↦ (x/4)*Real.log y) t :=
    continuousAt_const.mul (Real.continuousAt_log ht0)
  have hl : ContinuousAt (fun y : ℝ ↦ Real.cos ((x/4)*Real.log y)) t :=
    Real.continuous_cos.continuousAt.comp hl0
  have hs : Continuous (fun y : ℝ ↦
      2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*y))) := by fun_prop
  exact (hp.mul hl).mul hs.continuousAt

theorem integrableOn_realThetaFiniteIntegrand (x T : ℝ) (N : ℕ) :
    IntegrableOn (realThetaFiniteIntegrand x N) (Ioc 1 T) := by
  have hc := (continuousOn_realThetaFiniteIntegrand x N).mono
    (show Icc (1:ℝ) T⊆Ioi 0 from fun t ht ↦ zero_lt_one.trans_le ht.1)
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem realThetaCosineIntegral_finite_sum_error (x T : ℝ) (N : ℕ) :
    |(∫ t : ℝ in Ioc 1 T, realThetaCosineIntegrand x t)-
      (∫ t : ℝ in Ioc 1 T, realThetaFiniteIntegrand x N t)|≤
        4*Real.exp (-Real.pi*((N:ℝ)+1)^2)/(Real.pi*((N:ℝ)+1)^2) := by
  have hi := (integrableOn_realThetaCosineIntegrand x).mono_set
    (Ioc_subset_Ioi_self : Ioc (1:ℝ) T⊆Ioi 1)
  have hj := integrableOn_realThetaFiniteIntegrand x T N
  have hp : 0<Real.pi*((N:ℝ)+1)^2 := by positivity
  have hm : IntegrableOn (fun t : ℝ ↦ 4*Real.exp (-(Real.pi*((N:ℝ)+1)^2)*t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 hp).const_mul 4
  have hm' := hm.mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) T⊆Ioi 1)
  rw [← integral_sub hi hj]
  calc
    _ ≤ ∫ t : ℝ in Ioc 1 T, |realThetaCosineIntegrand x t-realThetaFiniteIntegrand x N t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ in Ioc 1 T, 4*Real.exp (-(Real.pi*((N:ℝ)+1)^2)*t) := by
      apply integral_mono_ae (hi.sub hj).abs hm'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [neg_mul] using realThetaCosineIntegrand_finite_error x N t ht.1.le
    _ ≤ ∫ t : ℝ in Ioi 1, 4*Real.exp (-(Real.pi*((N:ℝ)+1)^2)*t) :=
      setIntegral_mono_set hm (Filter.Eventually.of_forall (fun _ ↦ by positivity))
        (Filter.Eventually.of_forall (fun _ ht ↦ ht.1))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hp) 1]
      simp only [mul_one, neg_div_neg_eq, neg_mul]
      ring

theorem F_real_finite_theta_sum_integral_error (x T : ℝ) (N : ℕ) (hT : 1≤T) :
    |(F (x:ℂ)).re-(1-((1+x^2)/4)*
      (∫ t : ℝ in Ioc 1 T, realThetaFiniteIntegrand x N t))/8|≤
        (1+x^2)*(Real.exp (-Real.pi*T)+
          Real.exp (-Real.pi*((N:ℝ)+1)^2)/((N:ℝ)+1)^2)/(8*Real.pi) := by
  have ht := F_real_finite_theta_integral_error x T hT
  have hs := realThetaCosineIntegral_finite_sum_error x T N
  let A := (1-((1+x^2)/4)*(∫ t : ℝ in Ioc 1 T, realThetaCosineIntegrand x t))/8
  let B := (1-((1+x^2)/4)*(∫ t : ℝ in Ioc 1 T, realThetaFiniteIntegrand x N t))/8
  have hab : |A-B|≤((1+x^2)/32)*
      (4*Real.exp (-Real.pi*((N:ℝ)+1)^2)/(Real.pi*((N:ℝ)+1)^2)) := by
    have hid (a b : ℝ) : (1-((1+x^2)/4)*a)/8-(1-((1+x^2)/4)*b)/8=
        -((1+x^2)/32)*(a-b) := by ring
    dsimp [A,B]
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0≤(1+x^2)/32)]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  calc
    _ ≤ |(F (x:ℂ)).re-A|+|A-B| := abs_sub_le _ _ _
    _ ≤ (1+x^2)*Real.exp (-Real.pi*T)/(8*Real.pi)+
        ((1+x^2)/32)*(4*Real.exp (-Real.pi*((N:ℝ)+1)^2)/(Real.pi*((N:ℝ)+1)^2)) :=
      add_le_add ht hab
    _ = _ := by
      have hn : (N:ℝ)+1≠0 := by positivity
      field_simp [hn, Real.pi_ne_zero]
      <;> ring

end ReciprocalXi


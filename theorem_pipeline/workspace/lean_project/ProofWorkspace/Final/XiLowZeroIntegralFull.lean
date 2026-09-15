import ProofWorkspace.Final.XiLowZeroTaylorFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

def realLowZeroThetaTaylorPolynomial (x c : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (lowZeroThetaTaylorCoefficient x c n).re*(t-c)^n

def lowZeroThetaTaylorPanelValue (x c h : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (lowZeroThetaTaylorCoefficient x c n).re*
    ((h^(n+1)-(-h)^(n+1))/(n+1:ℕ))

theorem realLowZeroThetaTaylorPolynomial_eq_re (x c t : ℝ) (N : ℕ) :
    realLowZeroThetaTaylorPolynomial x c N t=(lowZeroThetaTaylorPolynomial x c N (t:ℂ)).re := by
  unfold realLowZeroThetaTaylorPolynomial lowZeroThetaTaylorPolynomial
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.mul_re]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem continuous_realLowZeroThetaTaylorPolynomial (x c : ℝ) (N : ℕ) :
    Continuous (realLowZeroThetaTaylorPolynomial x c N) := by
  unfold realLowZeroThetaTaylorPolynomial
  fun_prop

theorem integral_realLowZeroThetaTaylorPolynomial (x c h : ℝ) (N : ℕ) :
    (∫ t : ℝ in (c-h)..(c+h), realLowZeroThetaTaylorPolynomial x c N t)=
      lowZeroThetaTaylorPanelValue x c h N := by
  unfold realLowZeroThetaTaylorPolynomial lowZeroThetaTaylorPanelValue
  rw [intervalIntegral.integral_finset_sum (fun n hn ↦
    (show Continuous (fun t : ℝ ↦ (lowZeroThetaTaylorCoefficient x c n).re*(t-c)^n) by fun_prop).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ t^n), integral_pow]
  congr 2 <;> push_cast <;> ring

theorem realLowZeroThetaTaylor80_error (x c h t : ℝ) (hx : |x|≤60) (hc : 1≤c)
    (hh : h≤c/16) (ht : t∈Icc (c-h) (c+h)) :
    |realThetaFiniteIntegrand x 5 t-realLowZeroThetaTaylorPolynomial x c 80 t|≤1/(10:ℝ)^56 := by
  have ht0 : 0<t := by linarith [ht.1]
  have hz : ‖(t:ℂ)-(c:ℂ)‖≤c/16 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he := (Complex.abs_re_le_norm
    (complexThetaFiniteIntegrand x 5 (t:ℂ)-lowZeroThetaTaylorPolynomial x c 80 (t:ℂ))).trans
      (lowZeroThetaTaylor80_remainder_le x c t hx hc hz)
  simpa only [Complex.sub_re, complexThetaFiniteIntegrand_re x t 5 ht0,
    ← realLowZeroThetaTaylorPolynomial_eq_re] using he

theorem realLowZeroThetaTaylor80_panel_error (x c h : ℝ) (hx : |x|≤60) (hc : 1≤c)
    (hh0 : 0≤h) (hh : h≤c/16) :
    |(∫ t : ℝ in (c-h)..(c+h), realThetaFiniteIntegrand x 5 t)-
      lowZeroThetaTaylorPanelValue x c h 80|≤2*h/(10:ℝ)^56 := by
  have hab : c-h≤c+h := by linarith
  have hi : IntervalIntegrable (realThetaFiniteIntegrand x 5) volume (c-h) (c+h) :=
    ((continuousOn_realThetaFiniteIntegrand x 5).mono
      (show Icc (c-h) (c+h)⊆Ioi 0 from fun t ht ↦ by
        change 0<t
        linarith [ht.1])).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (realLowZeroThetaTaylorPolynomial x c 80) volume (c-h) (c+h) :=
    (continuous_realLowZeroThetaTaylorPolynomial x c 80).intervalIntegrable (c-h) (c+h)
  rw [← integral_realLowZeroThetaTaylorPolynomial, ← intervalIntegral.integral_sub hi hj]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=c-h) (b:=c+h) (C:=1/(10:ℝ)^56)
    (f:=fun t ↦ realThetaFiniteIntegrand x 5 t-realLowZeroThetaTaylorPolynomial x c 80 t) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs] using realLowZeroThetaTaylor80_error x c h t hx hc hh ⟨ht.1.le,ht.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0≤(c+h)-(c-h))] at hb
  convert hb using 1 <;> ring

theorem intervalIntegrable_lowZeroTheta_between (x a b : ℝ) (ha : 1≤a) (hab : a≤b) :
    IntervalIntegrable (realThetaFiniteIntegrand x 5) volume a b := by
  apply ((continuousOn_realThetaFiniteIntegrand x 5).mono ?_).intervalIntegrable_of_Icc hab
  intro t ht
  change 0<t
  linarith [ht.1]

theorem lowZeroThetaPanelIntegral_dyadic_sum (x : ℝ) (j : ℕ) :
    (∑ i ∈ Finset.range 8, ∫ t : ℝ in
      (theta48PanelCenter j i-theta48PanelHalfWidth j)..
      (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand x 5 t)=
      ∫ t : ℝ in (2:ℝ)^j..(2:ℝ)^(j+1), realThetaFiniteIntegrand x 5 t := by
  simp_rw [(theta48Panel_endpoints j _).1, (theta48Panel_endpoints j _).2]
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a:=theta48PanelEdge j) (n:=8) (f:=realThetaFiniteIntegrand x 5) (μ:=volume) (by
      intro k hk
      have hp : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
      have hn : 0≤(k:ℝ)*2^j := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      apply intervalIntegrable_lowZeroTheta_between x
      · unfold theta48PanelEdge
        nlinarith
      · unfold theta48PanelEdge
        push_cast
        nlinarith)
  simpa [theta48PanelEdge, pow_succ, mul_comm, one_add_one_eq_two] using he

def lowZeroThetaQuadrature80 (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8,
    lowZeroThetaTaylorPanelValue x (theta48PanelCenter j i) (theta48PanelHalfWidth j) 80

theorem lowZeroTheta_integral_panel_sum (x : ℝ) :
    (∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8, ∫ t : ℝ in
      (theta48PanelCenter j i-theta48PanelHalfWidth j)..
      (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand x 5 t)=
      ∫ t : ℝ in (1:ℝ)..32, realThetaFiniteIntegrand x 5 t := by
  simp_rw [lowZeroThetaPanelIntegral_dyadic_sum x]
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun j : ℕ ↦ (2:ℝ)^j) (n:=5) (f:=realThetaFiniteIntegrand x 5) (μ:=volume) (by
      intro k hk
      apply intervalIntegrable_lowZeroTheta_between x
      · exact one_le_pow₀ (by norm_num)
      · dsimp only
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k])
  convert he using 1 <;> norm_num

theorem lowZeroThetaQuadrature80_error (x : ℝ) (hx : |x|≤60) :
    |(∫ t : ℝ in Ioc 1 32, realThetaFiniteIntegrand x 5 t)-lowZeroThetaQuadrature80 x|≤31/(10:ℝ)^56 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤32),
    ← lowZeroTheta_integral_panel_sum x]
  unfold lowZeroThetaQuadrature80
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8,
        |(∫ t : ℝ in (theta48PanelCenter j i-theta48PanelHalfWidth j)..
          (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand x 5 t)-
          lowZeroThetaTaylorPanelValue x (theta48PanelCenter j i) (theta48PanelHalfWidth j) 80| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun j hj ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range 5, ∑ _i ∈ Finset.range 8,
        2*theta48PanelHalfWidth j/(10:ℝ)^56 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hc,hh0,hh⟩ := theta48Panel_bounds j i
      exact realLowZeroThetaTaylor80_panel_error x _ _ hx hc hh0 hh
    _ = _ := by norm_num [theta48PanelHalfWidth, Finset.sum_range_succ]

theorem F_lowZeroThetaQuadrature80_error (x : ℝ) (hx : |x|≤60) :
    |(F (x:ℂ)).re-(1-((1+x^2)/4)*lowZeroThetaQuadrature80 x)/8|≤3/(10:ℝ)^39 := by
  have ht := F_lowZero_finite_theta_truncation_error x hx
  have hq := lowZeroThetaQuadrature80_error x hx
  have hx2 : x^2≤3600 := by
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hx 2, sq_abs x]
  have hid (a b : ℝ) : (1-((1+x^2)/4)*a)/8-(1-((1+x^2)/4)*b)/8=
      -((1+x^2)/32)*(a-b) := by ring
  have he := abs_sub_le (F (x:ℂ)).re
    ((1-((1+x^2)/4)*(∫ t : ℝ in Ioc 1 32, realThetaFiniteIntegrand x 5 t))/8)
    ((1-((1+x^2)/4)*lowZeroThetaQuadrature80 x)/8)
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0≤(1+x^2)/32)] at he
  have hp := mul_le_mul_of_nonneg_left hq (show 0≤(1+x^2)/32 by positivity)
  have hscale : (1+x^2)/32*(31/(10:ℝ)^56)≤1/(10:ℝ)^39 := by
    nlinarith
  linarith


end ReciprocalXi

import ProofWorkspace.Final.XiThetaPanelIntegralFull
import ProofWorkspace.Final.XiThetaTruncationBudgetFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

def theta48PanelEdge (j i : ℕ) : ℝ := (1+(i:ℝ)/8)*2^j
def theta48PanelCenter (j i : ℕ) : ℝ := (17+2*(i:ℝ))*2^j/16
def theta48PanelHalfWidth (j : ℕ) : ℝ := 2^j/16

theorem theta48Panel_endpoints (j i : ℕ) :
    theta48PanelCenter j i-theta48PanelHalfWidth j=theta48PanelEdge j i ∧
    theta48PanelCenter j i+theta48PanelHalfWidth j=theta48PanelEdge j (i+1) := by
  constructor <;> simp only [theta48PanelCenter, theta48PanelHalfWidth, theta48PanelEdge,
    Nat.cast_add, Nat.cast_one] <;> ring

theorem theta48Panel_bounds (j i : ℕ) :
    1≤theta48PanelCenter j i ∧ 0≤theta48PanelHalfWidth j ∧
      theta48PanelHalfWidth j≤theta48PanelCenter j i/16 := by
  have hp : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
  have hi : (0:ℝ)≤(i:ℝ)*2^j := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  unfold theta48PanelCenter theta48PanelHalfWidth
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem intervalIntegrable_theta48_between (a b : ℝ) (ha : 1≤a) (hab : a≤b) :
    IntervalIntegrable (realThetaFiniteIntegrand 48 4) volume a b := by
  apply ((continuousOn_realThetaFiniteIntegrand 48 4).mono ?_).intervalIntegrable_of_Icc hab
  intro t ht
  change 0<t
  linarith [ht.1]

theorem theta48PanelIntegral_dyadic_sum (j : ℕ) :
    (∑ i ∈ Finset.range 8, ∫ t : ℝ in
      (theta48PanelCenter j i-theta48PanelHalfWidth j)..
      (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand 48 4 t)=
      ∫ t : ℝ in (2:ℝ)^j..(2:ℝ)^(j+1), realThetaFiniteIntegrand 48 4 t := by
  simp_rw [(theta48Panel_endpoints j _).1, (theta48Panel_endpoints j _).2]
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a:=theta48PanelEdge j) (n:=8) (f:=realThetaFiniteIntegrand 48 4) (μ:=volume) (by
      intro k hk
      have hp : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
      have hn : 0≤(k:ℝ)*2^j := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      apply intervalIntegrable_theta48_between
      · unfold theta48PanelEdge
        nlinarith
      · unfold theta48PanelEdge
        push_cast
        nlinarith)
  simpa [theta48PanelEdge, pow_succ, mul_comm, one_add_one_eq_two] using he

def theta48Quadrature40 : ℝ :=
  ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8,
    theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40

theorem theta48_integral_panel_sum :
    (∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8, ∫ t : ℝ in
      (theta48PanelCenter j i-theta48PanelHalfWidth j)..
      (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand 48 4 t)=
      ∫ t : ℝ in (1:ℝ)..16, realThetaFiniteIntegrand 48 4 t := by
  simp_rw [theta48PanelIntegral_dyadic_sum]
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun j : ℕ ↦ (2:ℝ)^j) (n:=4) (f:=realThetaFiniteIntegrand 48 4) (μ:=volume) (by
      intro k hk
      apply intervalIntegrable_theta48_between
      · exact one_le_pow₀ (by norm_num)
      · dsimp only
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k])
  convert he using 1 <;> norm_num

theorem theta48Quadrature40_error :
    |(∫ t : ℝ in Ioc 1 16, realThetaFiniteIntegrand 48 4 t)-theta48Quadrature40|≤15/(10:ℝ)^22 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤16),
    ← theta48_integral_panel_sum]
  unfold theta48Quadrature40
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8,
        |(∫ t : ℝ in (theta48PanelCenter j i-theta48PanelHalfWidth j)..
          (theta48PanelCenter j i+theta48PanelHalfWidth j), realThetaFiniteIntegrand 48 4 t)-
          theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun j hj ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range 4, ∑ _i ∈ Finset.range 8,
        2*theta48PanelHalfWidth j/(10:ℝ)^22 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hc,hh0,hh⟩ := theta48Panel_bounds j i
      exact realTheta48Taylor40_panel_error _ _ hc hh0 hh
    _ = _ := by norm_num [theta48PanelHalfWidth, Finset.sum_range_succ]

theorem F48_theta48Quadrature40_error :
    |(F (48:ℂ)).re-(1-(2305/4:ℝ)*theta48Quadrature40)/8|≤2/(10:ℝ)^16 := by
  have ht := F48_finite_theta_truncation_error
  have hq := theta48Quadrature40_error
  have hid (a b : ℝ) : (1-(2305/4:ℝ)*a)/8-(1-(2305/4:ℝ)*b)/8=-(2305/32:ℝ)*(a-b) := by ring
  have he := abs_sub_le (F (48:ℂ)).re
    ((1-(2305/4:ℝ)*(∫ t : ℝ in Ioc 1 16, realThetaFiniteIntegrand 48 4 t))/8)
    ((1-(2305/4:ℝ)*theta48Quadrature40)/8)
  rw [hid, abs_mul] at he
  norm_num at he
  linarith

end ReciprocalXi

import ProofWorkspace.Final.CurvatureBoundsFull
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Quantitative curvature control on the two-exponential tail

This file proves the error propagation and threshold arguments after the three
analytic remainder estimates in Section 4 of the source proof. The estimates
themselves, including their derivation from a convolution and an exponential
moment, remain hypotheses. No reciprocal-Xi theorem is postulated here.
-/

namespace ReciprocalXi

/-- Nonuniform version of the curvature perturbation bound: the errors in the
value and its first two derivatives may have three different upper bounds. -/
theorem curvatureJet_nonuniform_error_bound
    (p0 p1 p2 g0 g1 g2 N0 N1 N2 e0 e1 e2 : ℝ)
    (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (he0 : 0 ≤ e0) (_he1 : 0 ≤ e1) (_he2 : 0 ≤ e2)
    (hp0 : |p0| ≤ N0) (hp1 : |p1| ≤ N1) (hp2 : |p2| ≤ N2)
    (hr0 : |g0 - p0| ≤ e0) (hr1 : |g1 - p1| ≤ e1) (hr2 : |g2 - p2| ≤ e2) :
    |curvatureJet g0 g1 g2 - curvatureJet p0 p1 p2| ≤
      N0 * e2 + 2 * N1 * e1 + N2 * e0 + e1 ^ 2 + e0 * e2 := by
  let r0 := g0 - p0
  let r1 := g1 - p1
  let r2 := g2 - p2
  have h01 : |p0 * r2| ≤ N0 * e2 := by
    rw [abs_mul]
    exact mul_le_mul hp0 hr2 (abs_nonneg _) hN0
  have h02 : |r0 * p2| ≤ N2 * e0 := by
    rw [abs_mul]
    calc
      |r0| * |p2| ≤ |r0| * N2 := mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
      _ ≤ e0 * N2 := mul_le_mul_of_nonneg_right hr0 hN2
      _ = N2 * e0 := mul_comm _ _
  have h03 : |r0 * r2| ≤ e0 * e2 := by
    rw [abs_mul]
    exact mul_le_mul hr0 hr2 (abs_nonneg _) he0
  have h11 : |2 * p1 * r1| ≤ 2 * N1 * e1 := by
    calc
      |2 * p1 * r1| = 2 * |p1| * |r1| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * N1 * e1 := by gcongr
  have h12 : |r1 ^ 2| ≤ e1 ^ 2 := by
    rw [abs_pow]
    gcongr
  have hleft : |2 * p1 * r1 + r1 ^ 2| ≤ 2 * N1 * e1 + e1 ^ 2 :=
    (abs_add_le _ _).trans (add_le_add h11 h12)
  have hright : |p0 * r2 + r0 * p2 + r0 * r2| ≤
      N0 * e2 + N2 * e0 + e0 * e2 :=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add h01 h02)) h03)
  have hid : curvatureJet g0 g1 g2 - curvatureJet p0 p1 p2 =
      (2 * p1 * r1 + r1 ^ 2) - (p0 * r2 + r0 * p2 + r0 * r2) := by
    dsimp [r0, r1, r2, curvatureJet]
    ring
  rw [hid]
  calc
    |(2 * p1 * r1 + r1 ^ 2) - (p0 * r2 + r0 * p2 + r0 * r2)| ≤
        |2 * p1 * r1 + r1 ^ 2| + |p0 * r2 + r0 * p2 + r0 * r2| := abs_sub _ _
    _ ≤ (2 * N1 * e1 + e1 ^ 2) + (N0 * e2 + N2 * e0 + e0 * e2) :=
      add_le_add hleft hright
    _ = N0 * e2 + 2 * N1 * e1 + N2 * e0 + e1 ^ 2 + e0 * e2 := by ring

/-- The right-hand side of Section 4, equation (9), written explicitly. -/
noncomputable def tailCurvatureMajorant (A B a b R D0 D1 D2 x : ℝ) : ℝ :=
  A * (D2 + 2 * a * D1 + a ^ 2 * D0) * Real.exp (-(a + R) * x) +
  B * (D2 + 2 * b * D1 + b ^ 2 * D0) * Real.exp (-(b + R) * x) +
  (D1 ^ 2 + D0 * D2) * Real.exp (-2 * R * x)

/-- Equation (9): three derivative-remainder estimates imply the full curvature
error majorant. No curvature-error estimate is assumed. -/
theorem twoExponential_jet_error_bound
    (A B a b R D0 D1 D2 x g0 g1 g2 : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (h0 : |g0 - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x))
    (h1 : |g1 - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x))
    (h2 : |g2 - (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x)) :
    |curvatureJet g0 g1 g2 - A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x)| ≤
      tailCurvatureMajorant A B a b R D0 D1 D2 x := by
  let s := Real.exp (-a * x)
  let t := Real.exp (-b * x)
  let q := Real.exp (-R * x)
  have hs : 0 ≤ s := (Real.exp_pos _).le
  have ht : 0 ≤ t := (Real.exp_pos _).le
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hp0 : |A * s - B * t| ≤ A * s + B * t := by
    simpa only [abs_of_nonneg (mul_nonneg hA hs), abs_of_nonneg (mul_nonneg hB ht)]
      using abs_sub (A * s) (B * t)
  have hp1 : |-a * A * s + b * B * t| ≤ a * A * s + b * B * t := by
    have haa : 0 ≤ a * A * s := by positivity
    have hbb : 0 ≤ b * B * t := by positivity
    calc
      |-a * A * s + b * B * t| = |b * B * t - a * A * s| := by congr 1; ring
      _ ≤ |b * B * t| + |a * A * s| := abs_sub _ _
      _ = a * A * s + b * B * t := by
        rw [abs_of_nonneg hbb, abs_of_nonneg haa]
        ring
  have hp2 : |a ^ 2 * A * s - b ^ 2 * B * t| ≤ a ^ 2 * A * s + b ^ 2 * B * t := by
    have haa : 0 ≤ a ^ 2 * A * s := by positivity
    have hbb : 0 ≤ b ^ 2 * B * t := by positivity
    calc
      |a ^ 2 * A * s - b ^ 2 * B * t| ≤ |a ^ 2 * A * s| + |b ^ 2 * B * t| :=
        abs_sub _ _
      _ = a ^ 2 * A * s + b ^ 2 * B * t := by
        rw [abs_of_nonneg haa, abs_of_nonneg hbb]
  have he := curvatureJet_nonuniform_error_bound
    (A * s - B * t) (-a * A * s + b * B * t) (a ^ 2 * A * s - b ^ 2 * B * t)
    g0 g1 g2 (A * s + B * t) (a * A * s + b * B * t)
    (a ^ 2 * A * s + b ^ 2 * B * t) (D0 * q) (D1 * q) (D2 * q)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity)
    hp0 hp1 hp2 h0 h1 h2
  have habexp : s * t = Real.exp (-(a + b) * x) := by
    dsimp [s, t]
    rw [← Real.exp_add]
    congr 1
    ring
  have haRexp : s * q = Real.exp (-(a + R) * x) := by
    dsimp [s, q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hbRexp : t * q = Real.exp (-(b + R) * x) := by
    dsimp [t, q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hRRexp : q * q = Real.exp (-2 * R * x) := by
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [twoExponentialJet_curvature, mul_assoc (A * B * (b - a) ^ 2), habexp] at he
  convert he using 1
  unfold tailCurvatureMajorant
  rw [← haRexp, ← hbRexp, ← hRRexp]
  ring

/-- If the explicit majorant consumes at most half the leading curvature, at
least half that curvature remains. This is a consequence of the derivative
remainders, rather than a hypothesis asserting the desired curvature. -/
theorem twoExponential_curvature_ge_half_of_majorant
    (A B a b R D0 D1 D2 x g0 g1 g2 : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (h0 : |g0 - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x))
    (h1 : |g1 - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x))
    (h2 : |g2 - (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x))
    (hsmall : tailCurvatureMajorant A B a b R D0 D1 D2 x ≤
      A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) / 2) :
    A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) / 2 ≤ curvatureJet g0 g1 g2 := by
  have he := twoExponential_jet_error_bound A B a b R D0 D1 D2 x g0 g1 g2
    hA hB ha hb hD0 hD1 hD2 h0 h1 h2
  have hlower := (abs_le.mp he).1
  linarith

/-- The elementary logarithmic threshold used for each relative error term. -/
theorem expTailTerm_le_one_sixth (U r x : ℝ)
    (hU : 0 < U) (hr : 0 < r) (hx : Real.log (6 * U) / r ≤ x) :
    U * Real.exp (-r * x) ≤ 1 / 6 := by
  have hlog : Real.log (6 * U) ≤ r * x := by
    have hh := (div_le_iff₀ hr).mp hx
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity)] at he
  rw [show -r * x = -(r * x) by ring, Real.exp_neg]
  change U / Real.exp (r * x) ≤ 1 / 6
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- The same conservative maximum of three logarithmic thresholds and zero
used in the source proof. -/
noncomputable def tailThreshold (a b R U1 U2 U3 : ℝ) : ℝ :=
  max 0 (max (Real.log (6 * U1) / (R - b))
    (max (Real.log (6 * U2) / (R - a)) (Real.log (6 * U3) / (2 * R - a - b))))

/-- Beyond the explicit threshold, the sum of the three relative exponential
errors is at most one half. -/
theorem relative_tail_sum_le_half (a b R U1 U2 U3 x : ℝ)
    (hab : a < b) (hbR : b < R) (hU1 : 0 < U1) (hU2 : 0 < U2) (hU3 : 0 < U3)
    (hx : tailThreshold a b R U1 U2 U3 ≤ x) :
    U1 * Real.exp (-(R - b) * x) + U2 * Real.exp (-(R - a) * x) +
      U3 * Real.exp (-(2 * R - a - b) * x) ≤ 1 / 2 := by
  have hall : max (Real.log (6 * U1) / (R - b))
      (max (Real.log (6 * U2) / (R - a)) (Real.log (6 * U3) / (2 * R - a - b))) ≤ x :=
    (le_max_right _ _).trans hx
  have hx1 : Real.log (6 * U1) / (R - b) ≤ x := (le_max_left _ _).trans hall
  have hx23 : max (Real.log (6 * U2) / (R - a))
      (Real.log (6 * U3) / (2 * R - a - b)) ≤ x := (le_max_right _ _).trans hall
  have hx2 := (le_max_left _ _).trans hx23
  have hx3 := (le_max_right _ _).trans hx23
  have h1 := expTailTerm_le_one_sixth U1 (R - b) x hU1 (by linarith) hx1
  have h2 := expTailTerm_le_one_sixth U2 (R - a) x hU2 (by linarith) hx2
  have h3 := expTailTerm_le_one_sixth U3 (2 * R - a - b) x hU3 (by linarith) hx3
  linarith

/-- Three coefficient upper bounds give the source proof's relative-error sum
after the leading curvature is factored out. The inequalities here concern only
explicit constants, not the unknown function's curvature. -/
theorem tail_majorant_le_relative (A B a b R D0 D1 D2 U1 U2 U3 x : ℝ)
    (hc1 : A * (D2 + 2 * a * D1 + a ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U1)
    (hc2 : B * (D2 + 2 * b * D1 + b ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U2)
    (hc3 : D1 ^ 2 + D0 * D2 ≤ A * B * (b - a) ^ 2 * U3) :
    tailCurvatureMajorant A B a b R D0 D1 D2 x ≤
      A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) *
        (U1 * Real.exp (-(R - b) * x) + U2 * Real.exp (-(R - a) * x) +
          U3 * Real.exp (-(2 * R - a - b) * x)) := by
  have hexp1 : Real.exp (-(a + R) * x) =
      Real.exp (-(a + b) * x) * Real.exp (-(R - b) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp2 : Real.exp (-(b + R) * x) =
      Real.exp (-(a + b) * x) * Real.exp (-(R - a) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp3 : Real.exp (-2 * R * x) =
      Real.exp (-(a + b) * x) * Real.exp (-(2 * R - a - b) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 := mul_le_mul_of_nonneg_right hc1 (Real.exp_pos (-(a + R) * x)).le
  have h2 := mul_le_mul_of_nonneg_right hc2 (Real.exp_pos (-(b + R) * x)).le
  have h3 := mul_le_mul_of_nonneg_right hc3 (Real.exp_pos (-2 * R * x)).le
  have hh := add_le_add (add_le_add h1 h2) h3
  change tailCurvatureMajorant A B a b R D0 D1 D2 x ≤ _ at hh
  convert hh using 1
  rw [hexp1, hexp2, hexp3]
  ring

/-- The explicit logarithmic threshold makes the majorant at most half of the
leading curvature. -/
theorem tail_majorant_le_half_of_threshold (A B a b R D0 D1 D2 U1 U2 U3 x : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hab : a < b) (hbR : b < R)
    (hU1 : 0 < U1) (hU2 : 0 < U2) (hU3 : 0 < U3)
    (hc1 : A * (D2 + 2 * a * D1 + a ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U1)
    (hc2 : B * (D2 + 2 * b * D1 + b ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U2)
    (hc3 : D1 ^ 2 + D0 * D2 ≤ A * B * (b - a) ^ 2 * U3)
    (hx : tailThreshold a b R U1 U2 U3 ≤ x) :
    tailCurvatureMajorant A B a b R D0 D1 D2 x ≤
      A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) / 2 := by
  have hh := tail_majorant_le_relative A B a b R D0 D1 D2 U1 U2 U3 x hc1 hc2 hc3
  have hs := relative_tail_sum_le_half a b R U1 U2 U3 x hab hbR hU1 hU2 hU3 hx
  calc
    _ ≤ A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) *
        (U1 * Real.exp (-(R - b) * x) + U2 * Real.exp (-(R - a) * x) +
          U3 * Real.exp (-(2 * R - a - b) * x)) := hh
    _ ≤ A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Quantitative tail positivity derived from all three remainder bounds,
explicit coefficient bounds, and the logarithmic threshold. -/
theorem twoExponential_tail_curvature_positive
    (A B a b R D0 D1 D2 U1 U2 U3 x g0 g1 g2 : ℝ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hU1 : 0 < U1) (hU2 : 0 < U2) (hU3 : 0 < U3)
    (hc1 : A * (D2 + 2 * a * D1 + a ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U1)
    (hc2 : B * (D2 + 2 * b * D1 + b ^ 2 * D0) ≤ A * B * (b - a) ^ 2 * U2)
    (hc3 : D1 ^ 2 + D0 * D2 ≤ A * B * (b - a) ^ 2 * U3)
    (hx : tailThreshold a b R U1 U2 U3 ≤ x)
    (h0 : |g0 - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x))
    (h1 : |g1 - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x))
    (h2 : |g2 - (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x)) :
    0 < curvatureJet g0 g1 g2 := by
  have hsmall := tail_majorant_le_half_of_threshold A B a b R D0 D1 D2 U1 U2 U3 x
    hA.le hB.le hab hbR hU1 hU2 hU3 hc1 hc2 hc3 hx
  have hh := twoExponential_curvature_ge_half_of_majorant A B a b R D0 D1 D2 x g0 g1 g2
    hA.le hB.le ha.le (le_trans ha.le hab.le) hD0 hD1 hD2 h0 h1 h2 hsmall
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hab))
  have hlead : 0 < A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) / 2 := by positivity
  exact hlead.trans_le hh

/-- The first explicit relative-error coefficient from equation (10). -/
noncomputable def tailU1 (C a b D0 D1 D2 : ℝ) : ℝ :=
  (D2 + 2 * a * D1 + a ^ 2 * D0) / (C * a * (b - a) ^ 2)

/-- The second explicit relative-error coefficient from equation (10). -/
noncomputable def tailU2 (C a b D0 D1 D2 : ℝ) : ℝ :=
  (D2 + 2 * b * D1 + b ^ 2 * D0) / (C * b * (b - a) ^ 2)

/-- The third explicit relative-error coefficient from equation (10). -/
noncomputable def tailU3 (C a b D0 D1 D2 : ℝ) : ℝ :=
  (D1 ^ 2 + D0 * D2) / (C ^ 2 * a * b * (b - a) ^ 2)

private theorem multiply_coefficient_by_denominator_ratio (p q d u : ℝ)
    (hp : 0 ≤ p) (hd : 0 < d) (hu : 0 ≤ u) (hdq : d ≤ q) :
    p * u ≤ p * (q * (u / d)) := by
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    u = d * (u / d) := (mul_div_cancel₀ u (ne_of_gt hd)).symm
    _ ≤ q * (u / d) := mul_le_mul_of_nonneg_right hdq (div_nonneg hu hd.le)

/-- The inequalities `A ≥ Cb` and `B ≥ Ca` imply all three coefficient bounds
for the explicit constants actually used in the source proof. -/
theorem tail_coefficient_bounds_of_pole_lower_bounds (A B C a b D0 D1 D2 : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hab : a < b)
    (hA : C * b ≤ A) (hB : C * a ≤ B)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) :
    A * (D2 + 2 * a * D1 + a ^ 2 * D0) ≤
        A * B * (b - a) ^ 2 * tailU1 C a b D0 D1 D2 ∧
    B * (D2 + 2 * b * D1 + b ^ 2 * D0) ≤
        A * B * (b - a) ^ 2 * tailU2 C a b D0 D1 D2 ∧
    D1 ^ 2 + D0 * D2 ≤ A * B * (b - a) ^ 2 * tailU3 C a b D0 D1 D2 := by
  have hb : 0 < b := ha.trans hab
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hab))
  have hca : 0 ≤ D2 + 2 * a * D1 + a ^ 2 * D0 := by positivity
  have hcb : 0 ≤ D2 + 2 * b * D1 + b ^ 2 * D0 := by positivity
  have hcc : 0 ≤ D1 ^ 2 + D0 * D2 := by positivity
  constructor
  · have hdq : C * a * (b - a) ^ 2 ≤ B * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hB hsq.le
    have hh := multiply_coefficient_by_denominator_ratio A (B * (b - a) ^ 2)
      (C * a * (b - a) ^ 2) (D2 + 2 * a * D1 + a ^ 2 * D0)
      hA0 (by positivity) hca hdq
    unfold tailU1
    convert hh using 1
    ring
  constructor
  · have hdq : C * b * (b - a) ^ 2 ≤ A * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hA hsq.le
    have hh := multiply_coefficient_by_denominator_ratio B (A * (b - a) ^ 2)
      (C * b * (b - a) ^ 2) (D2 + 2 * b * D1 + b ^ 2 * D0)
      hB0 (by positivity) hcb hdq
    unfold tailU2
    convert hh using 1
    ring
  · have hprod : C ^ 2 * a * b ≤ A * B := by
      have hh := mul_le_mul hA hB (by positivity : 0 ≤ C * a) hA0
      convert hh using 1
      ring
    have hdq : C ^ 2 * a * b * (b - a) ^ 2 ≤ A * B * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hprod hsq.le
    have hh := multiply_coefficient_by_denominator_ratio 1 (A * B * (b - a) ^ 2)
      (C ^ 2 * a * b * (b - a) ^ 2) (D1 ^ 2 + D0 * D2)
      (by norm_num) (by positivity) hcc hdq
    unfold tailU3
    convert hh using 1 <;> ring

/-- Complete quantitative tail reduction using the source's explicit `U` values.
Its only function-dependent premises are the three analytic remainder bounds. -/
theorem twoExponential_tail_curvature_positive_of_pole_bounds
    (A B C a b R D0 D1 D2 x g0 g1 g2 : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (hA : C * b ≤ A) (hB : C * a ≤ B)
    (hD0 : 0 < D0) (hD1 : 0 ≤ D1) (hD2 : 0 < D2)
    (hx : tailThreshold a b R (tailU1 C a b D0 D1 D2)
      (tailU2 C a b D0 D1 D2) (tailU3 C a b D0 D1 D2) ≤ x)
    (h0 : |g0 - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x))
    (h1 : |g1 - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x))
    (h2 : |g2 - (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x)) :
    0 < curvatureJet g0 g1 g2 := by
  have hb : 0 < b := ha.trans hab
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hab))
  have hU1 : 0 < tailU1 C a b D0 D1 D2 := by unfold tailU1; positivity
  have hU2 : 0 < tailU2 C a b D0 D1 D2 := by unfold tailU2; positivity
  have hU3 : 0 < tailU3 C a b D0 D1 D2 := by unfold tailU3; positivity
  obtain ⟨hc1, hc2, hc3⟩ := tail_coefficient_bounds_of_pole_lower_bounds A B C a b D0 D1 D2
    hC ha hab hA hB hD0.le hD1 hD2.le
  exact twoExponential_tail_curvature_positive A B a b R D0 D1 D2
    (tailU1 C a b D0 D1 D2) (tailU2 C a b D0 D1 D2) (tailU3 C a b D0 D1 D2)
    x g0 g1 g2 hApos hBpos ha hab hbR hD0.le hD1 hD2.le
    hU1 hU2 hU3 hc1 hc2 hc3 hx h0 h1 h2

/-- The threshold includes zero, so its tail is a subset of the nonnegative
half-line on which the source's convolution remainder estimates apply. -/
theorem tailThreshold_nonneg (a b R U1 U2 U3 : ℝ) :
    0 ≤ tailThreshold a b R U1 U2 U3 := le_max_left _ _

/-- Function-level version: the two error jets are certified as the actual first
and second derivatives by `HasDerivAt`, and all remaining assumptions are the
source's coefficient, rate, threshold, and derivative-remainder premises. -/
theorem tail_function_curvature_positive
    (g : ℝ → ℝ) (A B C a b R D0 D1 D2 x g1 g2 : ℝ)
    (hg1 : HasDerivAt g g1 x) (hg2 : HasDerivAt (deriv g) g2 x)
    (hC : 0 < C) (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (hA : C * b ≤ A) (hB : C * a ≤ B)
    (hD0 : 0 < D0) (hD1 : 0 ≤ D1) (hD2 : 0 < D2)
    (hx : tailThreshold a b R (tailU1 C a b D0 D1 D2)
      (tailU2 C a b D0 D1 D2) (tailU3 C a b D0 D1 D2) ≤ x)
    (h0 : |g x - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x))
    (h1 : |g1 - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x))
    (h2 : |g2 - (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x)) :
    0 < curvatureJet (g x) (deriv g x) (deriv (deriv g) x) := by
  rw [hg1.deriv, hg2.deriv]
  exact twoExponential_tail_curvature_positive_of_pole_bounds A B C a b R D0 D1 D2
    x (g x) g1 g2 hC ha hab hbR hA hB hD0 hD1 hD2 hx h0 h1 h2

end ReciprocalXi

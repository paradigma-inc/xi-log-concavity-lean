import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
General, assumption-explicit reductions for the reciprocal-Xi proof.
No assertion in this module establishes the Xi-specific analytic estimates.
-/

namespace ReciprocalXi

/-- Exact overlap of the conservative published tail onset and the compact range. -/
theorem certified_ranges_overlap :
    (317649680434 : ℝ) / 100000000000 < (318 : ℝ) / 100 := by
  norm_num

/-- Glue compact and tail positivity for an even real-valued function. -/
theorem positive_of_even_compact_tail
    (H : ℝ → ℝ) (X B : ℝ)
    (heven : ∀ x, H (-x) = H x)
    (hoverlap : X ≤ B)
    (hcompact : ∀ x, 0 ≤ x → x ≤ B → 0 < H x)
    (htail : ∀ x, X ≤ x → 0 < H x) :
    ∀ x, 0 < H x := by
  have hnonneg : ∀ x, 0 ≤ x → 0 < H x := by
    intro x hx
    by_cases hxb : x ≤ B
    · exact hcompact x hx hxb
    · exact htail x (le_trans hoverlap (le_of_lt (lt_of_not_ge hxb)))
  intro x
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · have h := hnonneg (-x) (by linarith)
    simpa only [heven] using h

/-- The first derivative of log of a positive differentiable function. -/
theorem deriv_log_eq_jet
    (f f1 : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hpos : ∀ x, 0 < f x) :
    deriv (fun x => Real.log (f x)) = fun x => f1 x / f x := by
  funext x
  exact ((hf x).log (ne_of_gt (hpos x))).deriv

/-- Exact second derivative formula with all differentiability hypotheses visible. -/
theorem deriv2_log_eq_jet
    (f f1 f2 : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hpos : ∀ x, 0 < f x) (x : ℝ) :
    (deriv^[2] (fun y => Real.log (f y))) x =
      (f2 x * f x - f1 x * f1 x) / (f x) ^ 2 := by
  change deriv (deriv (fun y => Real.log (f y))) x = _
  rw [deriv_log_eq_jet f f1 hf hpos]
  exact ((hf1 x).div (hf x) (ne_of_gt (hpos x))).deriv

/-- Positive curvature implies strict log concavity for a positive C² function.
The curvature hypothesis is a parameter, not a theorem about the Xi density. -/
theorem strictConcaveOn_log_of_positive_curvature
    (f f1 f2 : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hpos : ∀ x, 0 < f x)
    (hcurv : ∀ x, 0 < (f1 x) ^ 2 - f x * f2 x) :
    StrictConcaveOn ℝ Set.univ (fun x => Real.log (f x)) := by
  apply strictConcaveOn_univ_of_deriv2_neg
  · exact continuous_iff_continuousAt.mpr
      (fun x => ((hf x).log (ne_of_gt (hpos x))).continuousAt)
  · intro x
    rw [deriv2_log_eq_jet f f1 f2 hf hf1 hpos x]
    apply div_neg_of_neg_of_pos
    · nlinarith [hcurv x]
    · exact sq_pos_of_pos (hpos x)

/-- Strict order-two translation inequality, derived from the curvature condition. -/
theorem translation_minor_pos_of_positive_curvature
    (f f1 f2 : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hpos : ∀ x, 0 < f x)
    (hcurv : ∀ x, 0 < (f1 x) ^ 2 - f x * f2 x)
    (t d e : ℝ) (hd : 0 < d) (he : 0 < e) :
    0 < f t * f (t + d - e) - f (t - e) * f (t + d) := by
  have hanti : StrictAnti (fun x => f1 x / f x) := by
    apply strictAnti_of_hasDerivAt_neg
      (fun x => (hf1 x).div (hf x) (ne_of_gt (hpos x)))
    intro x
    apply div_neg_of_neg_of_pos
    · nlinarith [hcurv x]
    · exact sq_pos_of_pos (hpos x)
  let g : ℝ → ℝ := fun x => Real.log (f x) - Real.log (f (x - e))
  have hg : ∀ x, HasDerivAt g
      (f1 x / f x - f1 (x - e) / f (x - e)) x := by
    intro x
    have hleft := (hf x).log (ne_of_gt (hpos x))
    have hright := ((hf (x - e)).log (ne_of_gt (hpos (x - e)))).comp x
      ((hasDerivAt_id x).sub_const e)
    simpa only [mul_one] using hleft.sub hright
  have hganti : StrictAnti g := by
    apply strictAnti_of_hasDerivAt_neg hg
    intro x
    exact sub_neg.mpr (hanti (by linarith : x - e < x))
  have hlt := hganti (by linarith : t < t + d)
  dsimp [g] at hlt
  apply sub_pos.mpr
  apply (Real.log_lt_log_iff
    (mul_pos (hpos (t - e)) (hpos (t + d)))
    (mul_pos (hpos t) (hpos (t + d - e)))).mp
  rw [Real.log_mul (ne_of_gt (hpos (t - e))) (ne_of_gt (hpos (t + d))),
      Real.log_mul (ne_of_gt (hpos t)) (ne_of_gt (hpos (t + d - e)))]
  linarith

/-- Positive determinant on arbitrary strictly increasing row/column nodes. -/
theorem pf2_minor_pos_of_positive_curvature
    (f f1 f2 : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hpos : ∀ x, 0 < f x)
    (hcurv : ∀ x, 0 < (f1 x) ^ 2 - f x * f2 x)
    (x1 x2 y1 y2 : ℝ) (hx : x1 < x2) (hy : y1 < y2) :
    0 < f (x1 - y1) * f (x2 - y2) - f (x1 - y2) * f (x2 - y1) := by
  have h := translation_minor_pos_of_positive_curvature f f1 f2 hf hf1 hpos hcurv
    (x1 - y1) (x2 - x1) (y2 - y1) (sub_pos.mpr hx) (sub_pos.mpr hy)
  have h1 : x1 - y1 + (x2 - x1) - (y2 - y1) = x2 - y2 := by ring
  have h2 : x1 - y1 - (y2 - y1) = x1 - y2 := by ring
  have h3 : x1 - y1 + (x2 - x1) = x2 - y1 := by ring
  rw [h1, h2, h3] at h
  exact h

end ReciprocalXi

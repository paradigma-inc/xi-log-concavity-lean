import ProofWorkspace.Final.XiRealBoundsFull
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantitative vertical zeta bounds from the actual Möbius inverse

An absolutely convergent L-series with coefficient norms at most one has
norm at most two on Re s≥2. Applying this to the constant-one and Möbius
series gives the required actual zeta lower bound without an assumed product.
-/

noncomputable section
open scoped LSeries.notation ArithmeticFunction.Moebius
namespace ReciprocalXi

theorem norm_LSeries_le_two (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (s : ℂ) (hs : 2 ≤ s.re) : ‖LSeries f s‖ ≤ 2 := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => hf n) (by linarith)
  have hterm (n : ℕ) : ‖LSeries.term f s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    have h₁ := LSeries.norm_term_le_of_re_le_re f (s := 2) (s' := s)
      (by simpa using hs) n
    have h₂ := LSeries.norm_term_le (f := f) (g := (1 : ℕ → ℂ)) 2
      (by simpa using hf n)
    have h := h₁.trans h₂
    by_cases hn : n = 0
    · subst n
      simp
    · simpa [LSeries.norm_term_eq, hn, Real.rpow_two] using h
  calc
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
      hsum.norm.tsum_le_tsum hterm hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem riemannZeta_norm_le_two (s : ℂ) (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 := by
  rw [← LSeries_one_eq_riemannZeta (by linarith : 1 < s.re)]
  exact norm_LSeries_le_two 1 (by simp) s hs

theorem moebius_LSeries_norm_le_two (s : ℂ) (hs : 2 ≤ s.re) :
    ‖LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ 2 := by
  apply norm_LSeries_le_two _ _ s hs
  intro n
  norm_cast
  exact ArithmeticFunction.abs_moebius_le_one

/-- The actual Möbius inverse series gives a quantitative lower bound. -/
theorem riemannZeta_norm_ge_half (s : ℂ) (hs : 2 ≤ s.re) :
    1 / 2 ≤ ‖riemannZeta s‖ := by
  have h := LSeries_one_mul_Lseries_moebius (by linarith : 1 < s.re)
  rw [LSeries_one_eq_riemannZeta (by linarith : 1 < s.re)] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_one] at hn
  have hm := moebius_LSeries_norm_le_two s hs
  have hb := mul_le_mul_of_nonneg_left hm (norm_nonneg (riemannZeta s))
  change ‖riemannZeta s‖ * ‖LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 at hn
  nlinarith

/-- The unbounded-strip zeta ratio estimate used by the source. -/
theorem riemannZeta_vertical_norm_comparison (s : ℂ) (hs : 2 ≤ s.re) :
    ‖riemannZeta (s.re : ℂ)‖ ≤ 4 * ‖riemannZeta s‖ := by
  have hl := riemannZeta_norm_ge_half s hs
  have hu := riemannZeta_norm_le_two (s.re : ℂ) hs
  linarith

end ReciprocalXi

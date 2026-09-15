import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem complex_linear_pair_perturbation (A B C D u v : ℂ) (deltaA deltaB : ℝ)
    (hA : ‖A-C‖≤deltaA) (hB : ‖B-D‖≤deltaB) :
    ‖(A*u-B*v)-(C*u-D*v)‖≤deltaA*‖u‖+deltaB*‖v‖ := by
  have hid : (A*u-B*v)-(C*u-D*v)=(A-C)*u-(B-D)*v := by ring
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

theorem complex_recurrence_step_error (A B a b u v w : ℂ) (rho : ℝ)
    (hr : ‖w-(A*u-B*v)‖≤rho) :
    ‖w-(A*a-B*b)‖≤rho+‖A‖*‖u-a‖+‖B‖*‖v-b‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub w (A*u-B*v) (A*a-B*b)
  have he : (A*u-B*v)-(A*a-B*b)=A*(u-a)-B*(v-b) := by ring
  rw [he] at ht
  have hn := norm_sub_le (A*(u-a)) (B*(v-b))
  rw [norm_mul, norm_mul] at hn
  linarith

theorem complex_second_order_error (a w A B : ℕ → ℂ) (U V E rho : ℕ → ℝ)
    (N : ℕ)
    (h0 : ‖w 0-a 0‖≤E 0) (h1 : ‖w 1-a 1‖≤E 1)
    (he : ∀ n, 0≤E n)
    (ha : ∀ n, n+2<N → a (n+2)=A n*a (n+1)-B n*a n)
    (hw : ∀ n, n+2<N → ‖w (n+2)-(A n*w (n+1)-B n*w n)‖≤rho n)
    (hu : ∀ n, n+2<N → ‖A n‖≤U n)
    (hv : ∀ n, n+2<N → ‖B n‖≤V n)
    (hE : ∀ n, n+2<N → rho n+U n*E (n+1)+V n*E n≤E (n+2)) :
    ∀ n, n<N → ‖w n-a n‖≤E n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases n with _|n
    · exact h0
    rcases n with _|n
    · exact h1
    have hnext : n+2<N := hn
    rw [ha n hnext]
    have ht := complex_recurrence_step_error (A n) (B n) (a (n+1)) (a n)
      (w (n+1)) (w n) (w (n+2)) (rho n) (hw n hnext)
    have hn1 := ih (n+1) (by omega) (by omega)
    have hn0 := ih n (by omega) (by omega)
    have hU0 : 0≤U n := (norm_nonneg _).trans (hu n hnext)
    have hV0 : 0≤V n := (norm_nonneg _).trans (hv n hnext)
    have ht1 := mul_le_mul (hu n hnext) hn1 (norm_nonneg _) hU0
    have ht0 := mul_le_mul (hv n hnext) hn0 (norm_nonneg _) hV0
    have hbound := hE n hnext
    linarith

end ReciprocalXi

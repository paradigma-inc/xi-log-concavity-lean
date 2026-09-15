import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
noncomputable section
open Set Complex Polynomial
namespace ReciprocalXi

theorem iteratedDeriv_cpow_slit (s z : ℂ) (n : ℕ) (hz : z∈Complex.slitPlane) :
    iteratedDeriv n (fun w : ℂ ↦ w^s) z =
      (descPochhammer ℤ n).smeval s*z^(s-n) := by
  suffices h : Set.EqOn (iteratedDerivWithin n (fun w : ℂ ↦ w^s) Complex.slitPlane)
      (fun w ↦ (descPochhammer ℤ n).smeval s*w^(s-n)) Complex.slitPlane by
    simpa only [iteratedDerivWithin_of_isOpen Complex.isOpen_slitPlane hz] using h hz
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have he : iteratedDerivWithin (n+1) (fun w : ℂ ↦ w^s) Complex.slitPlane =
        derivWithin (iteratedDerivWithin n (fun w : ℂ ↦ w^s) Complex.slitPlane) Complex.slitPlane := by
      ext w
      rw [iteratedDerivWithin_succ]
    rw [he]
    intro w hw
    rw [derivWithin_congr (fun _ hv ↦ ih hv) (ih hw),
      derivWithin_of_isOpen Complex.isOpen_slitPlane hw, deriv_const_mul_field']
    dsimp only
    rw [Complex.deriv_cpow_const hw]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show s-((n:ℂ)+1)=s-n-1 by ring, ← mul_assoc]
    congr 1
    simp [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_natCast]

def complexPowerExpAtom (s : ℂ) (lambda : ℝ) (z : ℂ) : ℂ :=
  z^s*Complex.exp ((-(lambda:ℂ))*z)

theorem complexPowerExpAtom_iteratedDeriv (s z : ℂ) (lambda : ℝ) (n : ℕ)
    (hz : z∈Complex.slitPlane) :
    iteratedDeriv n (complexPowerExpAtom s lambda) z =
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*
        ((descPochhammer ℤ i).smeval s*z^(s-i))*
        ((-(lambda:ℂ))^(n-i)*Complex.exp ((-(lambda:ℂ))*z)) := by
  have hp : AnalyticAt ℂ (fun w : ℂ ↦ w^s) z :=
    analyticAt_id.cpow analyticAt_const hz
  have he : ContDiff ℂ n (fun w : ℂ ↦ Complex.exp ((-(lambda:ℂ))*w)) := by fun_prop
  unfold complexPowerExpAtom
  rw [iteratedDeriv_fun_mul hp.contDiffAt he.contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_cpow_slit s z i hz, iteratedDeriv_cexp_const_mul]

end ReciprocalXi

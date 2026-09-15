import ProofWorkspace.Final.PowerExponentialODEFull
import ProofWorkspace.Final.XiThetaPanelIntegralFull

set_option autoImplicit false
noncomputable section
open Set Complex
namespace ReciprocalXi

def scaledPowerExpCoefficient (s z : ℂ) (lambda h : ℝ) (n : ℕ) : ℂ :=
  complexPowerExpTaylorCoefficient s z lambda n*(h:ℂ)^n

theorem scaledPowerExpCoefficient_zero (s z : ℂ) (lambda h : ℝ) :
    scaledPowerExpCoefficient s z lambda h 0=complexPowerExpAtom s lambda z := by
  simp [scaledPowerExpCoefficient, complexPowerExpTaylorCoefficient]

theorem scaledPowerExpCoefficient_one (s z : ℂ) (lambda h : ℝ)
    (hz : z∈Complex.slitPlane) :
    z*scaledPowerExpCoefficient s z lambda h 1=
      (s-(lambda:ℂ)*z)*(h:ℂ)*scaledPowerExpCoefficient s z lambda h 0 := by
  have he := complexPowerExpAtom_ode s z lambda hz
  simp only [scaledPowerExpCoefficient, complexPowerExpTaylorCoefficient,
    Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, pow_zero,
    mul_one, iteratedDeriv_zero, iteratedDeriv_one]
  linear_combination (h:ℂ)*he

theorem scaledPowerExpCoefficient_recurrence (s z : ℂ) (lambda h : ℝ) (n : ℕ)
    (hz : z∈Complex.slitPlane) :
    z*(n+2:ℕ)*scaledPowerExpCoefficient s z lambda h (n+2)=
      (s-(lambda:ℂ)*z-(n+1:ℕ))*(h:ℂ)*scaledPowerExpCoefficient s z lambda h (n+1)-
      (lambda:ℂ)*(h:ℂ)^2*scaledPowerExpCoefficient s z lambda h n := by
  have he := complexPowerExpTaylorCoefficient_recurrence s z lambda n hz
  unfold scaledPowerExpCoefficient
  simp only [pow_add, pow_one]
  linear_combination (h:ℂ)^(n+2)*he

theorem complexThetaFiniteIntegrand_atom_sum (x : ℝ) (N : ℕ) :
    complexThetaFiniteIntegrand x N=fun z : ℂ ↦
      2*(∑ k ∈ Finset.range N,
        complexPowerExpAtom (complexThetaExponent x) (Real.pi*((k:ℝ)+1)^2) z) := by
  funext z
  unfold complexThetaFiniteIntegrand complexPowerExpAtom
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem theta48TaylorCoefficient_scaled_atoms (c h : ℝ) (n : ℕ) (hc : 0<c) :
    theta48TaylorCoefficient c n*(h:ℂ)^n=
      2*(∑ k ∈ Finset.range 4,
        scaledPowerExpCoefficient (complexThetaExponent 48) (c:ℂ)
          (Real.pi*((k:ℝ)+1)^2) h n) := by
  have hz : (c:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc)
  have hd : ∀ k ∈ Finset.range 4, ContDiffAt ℂ n
      (complexPowerExpAtom (complexThetaExponent 48) (Real.pi*((k:ℝ)+1)^2)) (c:ℂ) :=
    fun k hk ↦ (complexPowerExpAtom_analyticAt _ _ _ hz).contDiffAt
  unfold theta48TaylorCoefficient
  rw [complexThetaFiniteIntegrand_atom_sum, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sum hd]
  unfold scaledPowerExpCoefficient complexPowerExpTaylorCoefficient
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem theta48TaylorPanelValue_scaled (c h : ℝ) (N : ℕ) :
    theta48TaylorPanelValue c h N=
      ∑ n ∈ Finset.range N, (h*(1-(-1:ℝ)^(n+1))/(n+1:ℕ))*
        (theta48TaylorCoefficient c n*(h:ℂ)^n).re := by
  unfold theta48TaylorPanelValue
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_pow, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show (-h)^(n+1)=(-1:ℝ)^(n+1)*h^(n+1) by rw [← mul_pow]; congr 1; ring,
    pow_succ h n]
  ring

end ReciprocalXi

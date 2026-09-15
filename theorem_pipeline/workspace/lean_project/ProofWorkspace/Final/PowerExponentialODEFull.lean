import ProofWorkspace.Final.PowerExponentialDerivativesFull

set_option autoImplicit false
noncomputable section
open Set Complex
namespace ReciprocalXi

theorem iteratedDeriv_id_mul_succ (f : ℂ → ℂ) (z : ℂ) (n : ℕ)
    (hf : ContDiffAt ℂ (n+1:ℕ) f z) :
    iteratedDeriv (n+1) (fun w : ℂ ↦ w*f w) z =
      z*iteratedDeriv (n+1) f z+(n+1:ℕ)*iteratedDeriv n f z := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf, Finset.sum_range_succ']
  simp only [iteratedDeriv_fun_id, Nat.add_eq_zero, Nat.one_ne_zero, and_false,
    if_false, Nat.add_right_cancel_iff, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, one_mul, if_true, mul_zero, zero_mul]
  rw [Finset.sum_eq_single 0]
  · simp
    ring
  · intro b hb hb0
    simp [hb0, show b+1≠1 by omega]
  · simp

theorem complexPowerExpAtom_analyticAt (s z : ℂ) (lambda : ℝ)
    (hz : z∈Complex.slitPlane) : AnalyticAt ℂ (complexPowerExpAtom s lambda) z := by
  exact (analyticAt_id.cpow analyticAt_const hz).mul
    ((analyticAt_const.mul analyticAt_id).cexp)

theorem complexPowerExpAtom_ode (s z : ℂ) (lambda : ℝ)
    (hz : z∈Complex.slitPlane) :
    z*deriv (complexPowerExpAtom s lambda) z=(s-(lambda:ℂ)*z)*complexPowerExpAtom s lambda z := by
  have hp : HasDerivAt (fun w : ℂ ↦ w^s) (s*z^(s-1)) z := by
    simpa using (hasDerivAt_id z).cpow_const hz (c:=s)
  have he : HasDerivAt (fun w : ℂ ↦ Complex.exp (-(lambda:ℂ)*w))
      (-(lambda:ℂ)*Complex.exp (-(lambda:ℂ)*z)) z := by
    convert ((hasDerivAt_id z).const_mul (-(lambda:ℂ))).cexp using 1 <;> simp <;> ring
  rw [show deriv (complexPowerExpAtom s lambda) z=
      (s*z^(s-1))*Complex.exp (-(lambda:ℂ)*z)+z^s*((-(lambda:ℂ))*Complex.exp (-(lambda:ℂ)*z))
      from (hp.mul he).deriv]
  have hpow : z*z^(s-1)=z^s := by
    calc
      _ = z^(s-1)*z^(1:ℂ) := by rw [Complex.cpow_one]; ring
      _ = z^((s-1)+1) := (Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hz)).symm
      _ = _ := by congr 1; ring
  unfold complexPowerExpAtom
  linear_combination s*Complex.exp (-(lambda:ℂ)*z)*hpow

theorem complexPowerExpAtom_derivative_recurrence (s z : ℂ) (lambda : ℝ) (n : ℕ)
    (hz : z∈Complex.slitPlane) :
    z*iteratedDeriv (n+2) (complexPowerExpAtom s lambda) z =
      (s-(lambda:ℂ)*z-(n+1:ℕ))*iteratedDeriv (n+1) (complexPowerExpAtom s lambda) z-
      (lambda:ℂ)*(n+1:ℕ)*iteratedDeriv n (complexPowerExpAtom s lambda) z := by
  let f := complexPowerExpAtom s lambda
  have ha := complexPowerExpAtom_analyticAt s z lambda hz
  have he : EqOn (fun w ↦ w*deriv f w) (fun w ↦ s*f w-(lambda:ℂ)*(w*f w)) Complex.slitPlane := by
    intro w hw
    have h := complexPowerExpAtom_ode s w lambda hw
    dsimp [f]
    linear_combination h
  have hid := he.iteratedDeriv_of_isOpen Complex.isOpen_slitPlane (n+1) hz
  have hs : ContDiffAt ℂ (n+1:ℕ) (fun w ↦ s*f w) z :=
    (analyticAt_const.mul ha).contDiffAt
  have hl : ContDiffAt ℂ (n+1:ℕ) (fun w ↦ (lambda:ℂ)*(w*f w)) z :=
    (analyticAt_const.mul (analyticAt_id.mul ha)).contDiffAt
  rw [iteratedDeriv_id_mul_succ (deriv f) z n ha.deriv.contDiffAt,
    iteratedDeriv_fun_sub hs hl,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_id_mul_succ f z n ha.contDiffAt] at hid
  simp only [← iteratedDeriv_succ'] at hid
  dsimp [f] at hid
  linear_combination hid

def complexPowerExpTaylorCoefficient (s z : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (complexPowerExpAtom s lambda) z/(n.factorial:ℂ)

theorem complexPowerExpTaylorCoefficient_recurrence (s z : ℂ) (lambda : ℝ) (n : ℕ)
    (hz : z∈Complex.slitPlane) :
    z*(n+2:ℕ)*complexPowerExpTaylorCoefficient s z lambda (n+2)=
      (s-(lambda:ℂ)*z-(n+1:ℕ))*complexPowerExpTaylorCoefficient s z lambda (n+1)-
      (lambda:ℂ)*complexPowerExpTaylorCoefficient s z lambda n := by
  have h := complexPowerExpAtom_derivative_recurrence s z lambda n hz
  unfold complexPowerExpTaylorCoefficient
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : ((n:ℂ)+1)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hn2 : ((n:ℂ)+2)≠0 := by exact_mod_cast (by omega : n+2≠0)
  convert congrArg (fun v : ℂ ↦ v/((n+1:ℕ)*n.factorial)) h using 1 <;>
    simp only [show n+2=(n+1)+1 by omega, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] <;>
    field_simp [hn, hn1, hn2] <;> ring_nf <;>
    field_simp [show (2:ℂ)+n≠0 by convert hn2 using 1 <;> ring] <;> ring

end ReciprocalXi

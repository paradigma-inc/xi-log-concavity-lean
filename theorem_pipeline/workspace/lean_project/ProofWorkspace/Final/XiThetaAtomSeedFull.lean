import ProofWorkspace.Final.XiThetaCoefficientFull
import ProofWorkspace.Final.ComplexExpCertificatesFull

set_option autoImplicit false
noncomputable section
open Complex Set
namespace ReciprocalXi

theorem complexPowerExpAtom_real_eq_exp (s : ℂ) (lambda c : ℝ) (hc : 0<c) :
    complexPowerExpAtom s lambda (c:ℂ)=
      Complex.exp (s*(Real.log c:ℂ)-(lambda*c:ℝ)) := by
  have hc0 : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  unfold complexPowerExpAtom
  rw [Complex.cpow_def_of_ne_zero hc0, ← Complex.ofReal_log hc.le,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem complexThetaExponent48_norm_le : ‖complexThetaExponent 48‖≤13 := by
  have h := Complex.norm_le_abs_re_add_abs_im (complexThetaExponent 48)
  rw [complexThetaExponent_re, complexThetaExponent_im] at h
  norm_num at h
  linarith

def theta48AtomExponent (c : ℝ) (k : ℕ) : ℂ :=
  complexThetaExponent 48*(Real.log c:ℂ)-(Real.pi*(k:ℝ)^2*c:ℝ)

def theta48AtomExponentApprox (c p q : ℝ) (k : ℕ) : ℂ :=
  complexThetaExponent 48*(q:ℂ)-(p*(k:ℝ)^2*c:ℝ)

theorem theta48AtomExponent_nonpos (c : ℝ) (k : ℕ) (hc : 1≤c) :
    (theta48AtomExponent c k).re≤0 := by
  have hl := Real.log_nonneg hc
  unfold theta48AtomExponent
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    complexThetaExponent_re, mul_zero, sub_zero]
  have hp : 0≤Real.pi*(k:ℝ)^2*c := by positivity
  nlinarith

theorem theta48AtomExponent_approx_error (c p q e d : ℝ) (k : ℕ) (hc : 0≤c)
    (hl : |Real.log c-q|≤e) (hp : |Real.pi-p|≤d) :
    ‖theta48AtomExponent c k-theta48AtomExponentApprox c p q k‖≤13*e+(k:ℝ)^2*c*d := by
  have hid : theta48AtomExponent c k-theta48AtomExponentApprox c p q k=
      complexThetaExponent 48*((Real.log c-q:ℝ):ℂ)-(((Real.pi-p)*(k:ℝ)^2*c:ℝ):ℂ) := by
    unfold theta48AtomExponent theta48AtomExponentApprox
    push_cast
    ring
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_pow]
  simp only [show |(k:ℝ)|=(k:ℝ) from abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hc]
  have hleft := mul_le_mul complexThetaExponent48_norm_le hl (abs_nonneg _) (by norm_num)
  have hright := mul_le_mul_of_nonneg_right hp (show 0≤(k:ℝ)^2*c by positivity)
  nlinarith

theorem theta48Atom_seed_certificate (c p q e d eta rho : ℝ) (k : ℕ) (w : ℕ → ℂ)
    (hc : 1≤c) (hl : |Real.log c-q|≤e) (hp : |Real.pi-p|≤d)
    (hu : (theta48AtomExponentApprox c p q k).re≤0)
    (hun : ‖theta48AtomExponentApprox c p q k/1024‖≤1)
    (heps : 13*e+(k:ℝ)^2*c*d≤1)
    (hseed : ‖w 0-complexExpTaylor40 (theta48AtomExponentApprox c p q k/1024)‖≤eta)
    (hstate : ∀ j, j<10 → ‖w j‖≤1)
    (hstep : ∀ j, j<10 → ‖w (j+1)-(w j)^2‖≤rho) :
    ‖w 10-complexPowerExpAtom (complexThetaExponent 48) (Real.pi*(k:ℝ)^2) (c:ℂ)‖≤
      1024*(eta+1/(10:ℝ)^47)+1023*rho+2*(13*e+(k:ℝ)^2*c*d) := by
  rw [complexPowerExpAtom_real_eq_exp _ _ _ (by linarith)]
  apply complexExp_scaled1024_certificate (theta48AtomExponentApprox c p q k)
    (theta48AtomExponent c k) w eta rho (13*e+(k:ℝ)^2*c*d) hu
    (theta48AtomExponent_nonpos c k hc) hun _ heps hseed hstate hstep
  rw [norm_sub_rev]
  exact theta48AtomExponent_approx_error c p q e d k (by linarith) hl hp

end ReciprocalXi

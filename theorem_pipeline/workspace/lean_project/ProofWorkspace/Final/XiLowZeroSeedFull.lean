import ProofWorkspace.Final.ComplexExpHighPrecisionFull
import ProofWorkspace.Final.XiThetaAtomSeedFull
import ProofWorkspace.Final.XiThetaPanelLogFull
import ProofWorkspace.Final.SourcePiMidpointFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem complexThetaExponent_lowZero_norm_le (x : ℝ) (hx : |x|≤60) :
    ‖complexThetaExponent x‖≤16 := by
  have h := Complex.norm_le_abs_re_add_abs_im (complexThetaExponent x)
  simp only [complexThetaExponent_re,complexThetaExponent_im,abs_div] at h
  norm_num at h
  linarith

def lowZeroAtomExponent (x c : ℝ) (k : ℕ) : ℂ :=
  complexThetaExponent x*(Real.log c:ℂ)-(Real.pi*(k:ℝ)^2*c:ℝ)

def lowZeroAtomExponentApprox (x c p q : ℝ) (k : ℕ) : ℂ :=
  complexThetaExponent x*(q:ℂ)-(p*(k:ℝ)^2*c:ℝ)

theorem lowZeroAtomExponent_approx_error (x c p q e d : ℝ) (k : ℕ)
    (hx : |x|≤60) (hc : 0≤c)
    (hl : |Real.log c-q|≤e) (hp : |Real.pi-p|≤d) :
    ‖lowZeroAtomExponent x c k-lowZeroAtomExponentApprox x c p q k‖≤
      16*e+(k:ℝ)^2*c*d := by
  have hid : lowZeroAtomExponent x c k-lowZeroAtomExponentApprox x c p q k=
      complexThetaExponent x*((Real.log c-q:ℝ):ℂ)-(((Real.pi-p)*(k:ℝ)^2*c:ℝ):ℂ) := by
    unfold lowZeroAtomExponent lowZeroAtomExponentApprox
    push_cast
    ring
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_pow]
  simp only [show |(k:ℝ)|=(k:ℝ) from abs_of_nonneg (Nat.cast_nonneg k),abs_of_nonneg hc]
  have hleft := mul_le_mul (complexThetaExponent_lowZero_norm_le x hx) hl
    (abs_nonneg _) (by norm_num)
  have hright := mul_le_mul_of_nonneg_right hp (show 0≤(k:ℝ)^2*c by positivity)
  nlinarith

theorem lowZeroAtomExponent_source_error (x c q : ℝ) (k : ℕ)
    (hx : |x|≤60) (hc0 : 0≤c) (hc : c≤32) (hk : k≤5)
    (hl : |Real.log c-q|≤5/(10:ℝ)^70) :
    ‖lowZeroAtomExponent x c k-lowZeroAtomExponentApprox x c sourcePiMidpoint q k‖≤
      1/(10:ℝ)^68 := by
  have hp : |Real.pi-(sourcePiMidpoint:ℝ)|≤1/(10:ℝ)^150 := by
    simpa only [abs_sub_comm] using sourcePiMidpoint_error
  have h := lowZeroAtomExponent_approx_error x c sourcePiMidpoint q
    (5/(10:ℝ)^70) (1/(10:ℝ)^150) k hx hc0 hl hp
  have hkR : (k:ℝ)≤5 := by exact_mod_cast hk
  have hk2 : (k:ℝ)^2≤25 := by
    nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  have hkprod : (k:ℝ)^2*c≤800 := by
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (k:ℝ))]
  apply h.trans
  nlinarith

theorem lowZeroAtom_relative_seed_error (x c q : ℝ) (k : ℕ) (w : ℂ)
    (hx : |x|≤60) (hc0 : 1≤c) (hc : c≤32) (hk : k≤5)
    (hl : |Real.log c-q|≤5/(10:ℝ)^70)
    (hw : ‖w-Complex.exp (lowZeroAtomExponentApprox x c sourcePiMidpoint q k)‖≤
      1/(10:ℝ)^90) :
    ‖w-complexPowerExpAtom (complexThetaExponent x) (Real.pi*(k:ℝ)^2) (c:ℂ)‖≤
      1/(10:ℝ)^90+(2/(10:ℝ)^68)*(‖w‖+1/(10:ℝ)^90) := by
  have hi := lowZeroAtomExponent_source_error x c q k hx (by linarith) hc hk hl
  have he := complexExp_relative_input_error
    (lowZeroAtomExponentApprox x c sourcePiMidpoint q k)
    (lowZeroAtomExponent x c k) w (1/(10:ℝ)^90) (1/(10:ℝ)^68) hw
    (by rw [norm_sub_rev]; exact hi) (by norm_num)
  rw [complexPowerExpAtom_real_eq_exp _ _ _ (by linarith)]
  dsimp only [lowZeroAtomExponent] at he
  convert he using 1 <;> ring

end ReciprocalXi

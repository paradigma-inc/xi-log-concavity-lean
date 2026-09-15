import ProofWorkspace.Final.XiThetaPanelLogFull
import ProofWorkspace.Final.XiThetaAtomSeedFull
import ProofWorkspace.Final.SourcePiMidpointFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem theta48PanelCenter_le_sixteen (j i : ℕ) (hj : j<4) (hi : i<8) :
    theta48PanelCenter j i≤16 := by
  have hj3 : j≤3 := by omega
  have hp : (2:ℝ)^j≤8 := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj3 using 1 <;> norm_num
  have hp0 : (0:ℝ)≤2^j := by positivity
  have hi7 : (i:ℝ)≤7 := by exact_mod_cast (by omega : i≤7)
  have hm := mul_le_mul_of_nonneg_right hi7 hp0
  unfold theta48PanelCenter
  nlinarith

theorem theta48PanelHalfWidth_le_half (j : ℕ) (hj : j<4) :
    theta48PanelHalfWidth j≤1/2 := by
  have hj3 : j≤3 := by omega
  have hp : (2:ℝ)^j≤8 := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj3 using 1 <;> norm_num
  unfold theta48PanelHalfWidth
  linarith

theorem theta48PanelAtom_exponent_error (j : ℕ) (i : Fin 8) (k : ℕ)
    (hj : j<4) (hk : k≤4) :
    ‖theta48AtomExponent (theta48PanelCenter j i) k-
      theta48AtomExponentApprox (theta48PanelCenter j i) sourcePiMidpoint
        (theta48PanelLogSeed j i) k‖≤1/(10:ℝ)^68 := by
  have hc := (theta48Panel_bounds j i).1
  have hc16 := theta48PanelCenter_le_sixteen j i hj i.isLt
  have hk4 : (k:ℝ)≤4 := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hk2 : (k:ℝ)^2≤16 := by nlinarith
  have hp : |Real.pi-(sourcePiMidpoint:ℝ)|≤1/(10:ℝ)^150 := by
    simpa only [abs_sub_comm] using sourcePiMidpoint_error
  have he := theta48AtomExponent_approx_error (theta48PanelCenter j i)
    sourcePiMidpoint (theta48PanelLogSeed j i) (4/(10:ℝ)^70) (1/(10:ℝ)^150)
    k (by linarith) (theta48PanelLogSeed_error_uniform j i hj) hp
  have hm : (k:ℝ)^2*theta48PanelCenter j i≤256 := by
    nlinarith [mul_le_mul hk2 hc16 (by linarith : 0≤theta48PanelCenter j i) (by norm_num)]
  apply he.trans
  nlinarith

theorem theta48PanelAtom_seed_error (j : ℕ) (i : Fin 8) (k : ℕ) (w : ℂ)
    (hj : j<4) (hk : k≤4)
    (hw : ‖w-Complex.exp (theta48AtomExponentApprox (theta48PanelCenter j i)
      sourcePiMidpoint (theta48PanelLogSeed j i) k)‖≤1/(10:ℝ)^43) :
    ‖w-complexPowerExpAtom (complexThetaExponent 48) (Real.pi*(k:ℝ)^2)
      (theta48PanelCenter j i:ℂ)‖≤1/(10:ℝ)^42 := by
  have hc := (theta48Panel_bounds j i).1
  have he := theta48PanelAtom_exponent_error j i k hj hk
  rw [norm_sub_rev] at he
  have hexp := complexExp_input_error
    (theta48AtomExponentApprox (theta48PanelCenter j i) sourcePiMidpoint (theta48PanelLogSeed j i) k)
    (theta48AtomExponent (theta48PanelCenter j i) k) (1/(10:ℝ)^68)
    (theta48AtomExponent_nonpos _ _ hc) he (by norm_num)
  rw [complexPowerExpAtom_real_eq_exp _ _ _ (by linarith)]
  have ht := norm_sub_le_norm_sub_add_norm_sub w
    (Complex.exp (theta48AtomExponentApprox (theta48PanelCenter j i)
      sourcePiMidpoint (theta48PanelLogSeed j i) k))
    (Complex.exp (theta48AtomExponent (theta48PanelCenter j i) k))
  change ‖w-Complex.exp (theta48AtomExponent (theta48PanelCenter j i) k)‖≤_
  linarith

end ReciprocalXi

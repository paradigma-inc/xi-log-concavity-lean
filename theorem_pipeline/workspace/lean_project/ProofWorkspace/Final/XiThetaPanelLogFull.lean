import ProofWorkspace.Final.XiThetaLogSeedsFull
import ProofWorkspace.Final.XiThetaDyadicIntegralFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def thetaLogBaseSeed : Fin 8 → ℚ :=
  ![thetaLogBase0Seed, thetaLogBase1Seed, thetaLogBase2Seed, thetaLogBase3Seed,
    thetaLogBase4Seed, thetaLogBase5Seed, thetaLogBase6Seed, thetaLogBase7Seed]

theorem thetaLogBaseSeed_error (i : Fin 8) :
    |Real.log ((17+2*(i:ℝ))/16)-(thetaLogBaseSeed i:ℝ)|≤1/(10:ℝ)^70 := by
  fin_cases i
  · convert thetaLogBase0Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase1Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase2Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase3Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase4Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase5Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase6Seed_error using 1 <;> norm_num [thetaLogBaseSeed]
  · convert thetaLogBase7Seed_error using 1 <;> norm_num [thetaLogBaseSeed]

theorem thetaLogBaseSeed_bounds (i : Fin 8) :
    0≤thetaLogBaseSeed i ∧ thetaLogBaseSeed i≤7/10 := by
  fin_cases i <;> norm_num [thetaLogBaseSeed, thetaLogBase0Seed, thetaLogBase1Seed,
    thetaLogBase2Seed, thetaLogBase3Seed, thetaLogBase4Seed, thetaLogBase5Seed,
    thetaLogBase6Seed, thetaLogBase7Seed]

def theta48PanelLogSeed (j : ℕ) (i : Fin 8) : ℚ :=
  j*thetaLogTwoSeed+thetaLogBaseSeed i

theorem theta48PanelLogSeed_error (j : ℕ) (i : Fin 8) :
    |Real.log (theta48PanelCenter j i)-(theta48PanelLogSeed j i:ℝ)|≤
      (j+1:ℕ)/(10:ℝ)^70 := by
  have hi : (0:ℝ)<(17+2*(i:ℝ))/16 := by positivity
  have he : theta48PanelCenter j i=(2:ℝ)^j*((17+2*(i:ℝ))/16) := by
    unfold theta48PanelCenter
    ring
  rw [he, Real.log_mul (by positivity) hi.ne', Real.log_pow]
  have hid : (j:ℝ)*Real.log 2+Real.log ((17+2*(i:ℝ))/16)-(theta48PanelLogSeed j i:ℝ)=
      (j:ℝ)*(Real.log 2-(thetaLogTwoSeed:ℝ))+
        (Real.log ((17+2*(i:ℝ))/16)-(thetaLogBaseSeed i:ℝ)) := by
    unfold theta48PanelLogSeed
    push_cast
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  have h1 := mul_le_mul_of_nonneg_left thetaLogTwoSeed_error (Nat.cast_nonneg j : (0:ℝ)≤j)
  have h2 := thetaLogBaseSeed_error i
  push_cast
  linarith

theorem theta48PanelLogSeed_error_uniform (j : ℕ) (i : Fin 8) (hj : j<4) :
    |Real.log (theta48PanelCenter j i)-(theta48PanelLogSeed j i:ℝ)|≤4/(10:ℝ)^70 := by
  apply (theta48PanelLogSeed_error j i).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (by omega : j+1≤4)

theorem theta48PanelLogSeed_bounds (j : ℕ) (i : Fin 8) (hj : j<4) :
    0≤theta48PanelLogSeed j i ∧ theta48PanelLogSeed j i≤3 := by
  have h2 : 0≤thetaLogTwoSeed ∧ thetaLogTwoSeed≤7/10 := by norm_num [thetaLogTwoSeed]
  have hi := thetaLogBaseSeed_bounds i
  have hj0 : (0:ℚ)≤j := Nat.cast_nonneg j
  have hj3 : (j:ℚ)≤3 := by exact_mod_cast (by omega : j≤3)
  unfold theta48PanelLogSeed
  constructor
  · exact add_nonneg (mul_nonneg hj0 h2.1) hi.1
  · nlinarith

end ReciprocalXi

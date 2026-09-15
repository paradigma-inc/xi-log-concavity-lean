import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def complexExpTaylor40 (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 40, z^n/(n.factorial:ℂ)

theorem complexExpTaylor40_error (z : ℂ) (hz : ‖z‖≤1) :
    ‖Complex.exp z-complexExpTaylor40 z‖≤1/(10:ℝ)^47 := by
  have h := Complex.exp_bound hz (by norm_num : 0<40)
  have hp : ‖z‖^40≤1 := pow_le_one₀ (norm_nonneg _) hz
  apply h.trans
  calc
    _ ≤ 1*((40+1:ℕ):ℝ)*((40:ℕ).factorial*40:ℝ)⁻¹ := by
      convert mul_le_mul_of_nonneg_right hp
        (show 0≤((40+1:ℕ):ℝ)*((40:ℕ).factorial*40:ℝ)⁻¹ by positivity) using 1 <;> ring
    _ ≤ _ := by norm_num

theorem complexExp_input_error (u v : ℂ) (epsilon : ℝ)
    (hv : v.re≤0) (herror : ‖u-v‖≤epsilon) (heps : epsilon≤1) :
    ‖Complex.exp u-Complex.exp v‖≤2*epsilon := by
  have hn : ‖Complex.exp v‖≤1 := by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hv
  have he : Complex.exp u-Complex.exp v=Complex.exp v*(Complex.exp (u-v)-1) := by
    rw [mul_sub, ← Complex.exp_add]
    simp
  rw [he, norm_mul]
  calc
    _ ≤ 1*‖Complex.exp (u-v)-1‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ 2*‖u-v‖ := by simpa using Complex.norm_exp_sub_one_le (herror.trans heps)
    _ ≤ _ := mul_le_mul_of_nonneg_left herror (by norm_num)

theorem complex_square_error (a b : ℂ) (ha : ‖a‖≤1) (hb : ‖b‖≤1) :
    ‖a^2-b^2‖≤2*‖a-b‖ := by
  rw [sq_sub_sq, norm_mul]
  have hsum : ‖a+b‖≤2 := (norm_add_le _ _).trans (by linarith)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum (norm_nonneg (a-b))

theorem complex_rounded_squaring_error (z : ℂ) (w : ℕ → ℂ) (eta rho : ℝ)
    (k : ℕ) (hz : ‖z‖≤1) (hw0 : ‖w 0-z‖≤eta)
    (hstate : ∀ j, j<k → ‖w j‖≤1)
    (hstep : ∀ j, j<k → ‖w (j+1)-(w j)^2‖≤rho) :
    ‖w k-z^(2^k)‖≤(2:ℝ)^k*eta+((2:ℝ)^k-1)*rho := by
  induction k with
  | zero => simpa using hw0
  | succ k ih =>
    have hi := ih (fun j hj ↦ hstate j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj))
    have he := complex_square_error (w k) (z^(2^k)) (hstate k (Nat.lt_succ_self k))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz)
    have ht := norm_sub_le_norm_sub_add_norm_sub (w (k+1)) ((w k)^2) ((z^(2^k))^2)
    have hp : (z^(2^k))^2=z^(2^(k+1)) := by rw [← pow_mul, pow_succ]
    rw [hp] at ht he
    have hs := hstep k (Nat.lt_succ_self k)
    rw [show (2:ℝ)^(k+1)=(2:ℝ)^k*2 from pow_succ _ _]
    linarith

theorem complexExp_scaled1024_certificate (u v : ℂ) (w : ℕ → ℂ)
    (eta rho epsilon : ℝ) (hu : u.re≤0) (hv : v.re≤0)
    (hun : ‖u/(1024:ℂ)‖≤1) (hinput : ‖u-v‖≤epsilon) (heps : epsilon≤1)
    (hseed : ‖w 0-complexExpTaylor40 (u/1024)‖≤eta)
    (hstate : ∀ j, j<10 → ‖w j‖≤1)
    (hstep : ∀ j, j<10 → ‖w (j+1)-(w j)^2‖≤rho) :
    ‖w 10-Complex.exp v‖≤1024*(eta+1/(10:ℝ)^47)+1023*rho+2*epsilon := by
  have hu0 : ‖Complex.exp (u/1024)‖≤1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa using div_nonpos_of_nonpos_of_nonneg hu (by norm_num : (0:ℝ)≤1024)
  have h0 : ‖w 0-Complex.exp (u/1024)‖≤eta+1/(10:ℝ)^47 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (w 0) (complexExpTaylor40 (u/1024)) (Complex.exp (u/1024))
    have he := complexExpTaylor40_error (u/1024) hun
    rw [norm_sub_rev] at he
    linarith
  have hp := complex_rounded_squaring_error (Complex.exp (u/1024)) w
    (eta+1/(10:ℝ)^47) rho 10 hu0 h0 hstate hstep
  have he : (Complex.exp (u/1024))^(2^10)=Complex.exp u := by
    rw [← Complex.exp_nat_mul]
    norm_num
    congr 1
    ring
  rw [he] at hp
  have hd := complexExp_input_error u v epsilon hv hinput heps
  have ht := norm_sub_le_norm_sub_add_norm_sub (w 10) (Complex.exp u) (Complex.exp v)
  norm_num at hp
  linarith

end ReciprocalXi

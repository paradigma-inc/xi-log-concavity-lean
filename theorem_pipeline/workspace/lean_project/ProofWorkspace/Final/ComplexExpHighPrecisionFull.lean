import ProofWorkspace.Final.RationalComplexExpSeedFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem complexExpTaylor40_small_error (z : ℂ) (hz : ‖z‖≤1/16) :
    ‖Complex.exp z-complexExpTaylor40 z‖≤1/(10:ℝ)^95 := by
  have h := Complex.exp_bound (show ‖z‖≤1 by linarith) (by norm_num : 0<40)
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz 40
  apply h.trans
  calc
    _ ≤ (1/16:ℝ)^40*((40+1:ℕ):ℝ)*((40:ℕ).factorial*40:ℝ)⁻¹ := by
      convert mul_le_mul_of_nonneg_right hp
        (show 0≤((40+1:ℕ):ℝ)*((40:ℕ).factorial*40:ℝ)⁻¹ by positivity) using 1 <;> ring
    _ ≤ _ := by norm_num

theorem complexExp_relative_input_error (u v w : ℂ) (eta epsilon : ℝ)
    (hseed : ‖w-Complex.exp u‖≤eta)
    (hinput : ‖u-v‖≤epsilon) (heps : epsilon≤1) :
    ‖w-Complex.exp v‖≤eta+2*epsilon*(‖w‖+eta) := by
  have heps0 : 0≤epsilon := (norm_nonneg _).trans hinput
  have hn : ‖Complex.exp u‖≤‖w‖+eta := by
    have h := norm_sub_le_norm_sub_add_norm_sub (Complex.exp u) w 0
    rw [sub_zero,sub_zero,norm_sub_rev (Complex.exp u)] at h
    linarith
  have harg : ‖v-u‖≤1 := by rw [norm_sub_rev]; exact hinput.trans heps
  have hd := Complex.norm_exp_sub_one_le harg
  have he : Complex.exp v-Complex.exp u=Complex.exp u*(Complex.exp (v-u)-1) := by
    rw [mul_sub, ← Complex.exp_add]
    simp
  have hb : ‖Complex.exp u-Complex.exp v‖≤2*epsilon*(‖w‖+eta) := by
    rw [norm_sub_rev,he,norm_mul]
    have hp : ‖Complex.exp (v-u)-1‖≤2*epsilon := by
      rw [norm_sub_rev v u] at hd
      linarith
    have h := mul_le_mul hn hp (norm_nonneg _) (by linarith [norm_nonneg (Complex.exp u)])
    nlinarith
  exact (norm_sub_le_norm_sub_add_norm_sub w (Complex.exp u) (Complex.exp v)).trans
    (add_le_add hseed hb)

theorem complexExp_scaled65536_highPrecision_error (u : ℂ) (w : ℕ → ℂ)
    (hu : u.re≤0) (hun : ‖u/65536‖≤1/16)
    (hseed : ‖w 0-complexExpTaylor40 (u/65536)‖≤2/(10:ℝ)^160)
    (hstate : ∀ j, j<16 → ‖w j‖≤1)
    (hstep : ∀ j, j<16 → ‖w (j+1)-(w j)^2‖≤2/(10:ℝ)^160) :
    ‖w 16-Complex.exp u‖≤1/(10:ℝ)^90 := by
  have hu0 : ‖Complex.exp (u/65536)‖≤1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa using div_nonpos_of_nonpos_of_nonneg hu (by norm_num : (0:ℝ)≤65536)
  have h0 : ‖w 0-Complex.exp (u/65536)‖≤2/(10:ℝ)^160+1/(10:ℝ)^95 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (w 0) (complexExpTaylor40 (u/65536)) (Complex.exp (u/65536))
    have he := complexExpTaylor40_small_error (u/65536) hun
    rw [norm_sub_rev] at he
    linarith
  have hp := complex_rounded_squaring_error (Complex.exp (u/65536)) w
    (2/(10:ℝ)^160+1/(10:ℝ)^95) (2/(10:ℝ)^160) 16 hu0 h0 hstate hstep
  have he : (Complex.exp (u/65536))^(2^16)=Complex.exp u := by
    rw [← Complex.exp_nat_mul]
    norm_num
    congr 1
    ring
  rw [he] at hp
  exact hp.trans (by norm_num)

def ratComplexExpHighPrecisionValid (u : ℚ × ℚ) (w : ℕ → ℚ × ℚ) : Prop :=
  u.1≤0 ∧
  (ratComplexDivNat u 65536).1^2+(ratComplexDivNat u 65536).2^2≤1/256 ∧
  (|(w 0).1-(ratComplexExpTaylorScan (ratComplexDivNat u 65536) 40).1| +
    |(w 0).2-(ratComplexExpTaylorScan (ratComplexDivNat u 65536) 40).2| ≤2/(10:ℚ)^160) ∧
  (∀ j : Fin 16, (w j).1^2+(w j).2^2≤1) ∧
  (∀ j : Fin 16,
    |(w ((j:ℕ)+1)).1-(ratComplexMul (w j) (w j)).1| +
    |(w ((j:ℕ)+1)).2-(ratComplexMul (w j) (w j)).2| ≤2/(10:ℚ)^160)

theorem ratComplexExpHighPrecisionValid_error (u : ℚ × ℚ) (w : ℕ → ℚ × ℚ)
    (h : ratComplexExpHighPrecisionValid u w) :
    ‖ratComplexValue (w 16)-Complex.exp (ratComplexValue u)‖≤1/(10:ℝ)^90 := by
  obtain ⟨hu,hun,hs,hw,hr⟩ := h
  have hre : (ratComplexValue u).re≤0 := by rw [ratComplexValue_re]; exact_mod_cast hu
  have hnorm : ‖ratComplexValue u/65536‖≤1/16 := by
    let q := ratComplexDivNat u 65536
    have he : ‖ratComplexValue q‖^2=(q.1:ℝ)^2+(q.2:ℝ)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, ratComplexValue_re, ratComplexValue_im]
      ring
    have hq' : (q.1:ℝ)^2+(q.2:ℝ)^2≤1/256 := by
      have hqrat : q.1^2+q.2^2≤(1/256:ℚ) := hun
      have hcast := (Rat.cast_le (K:=ℝ)).mpr hqrat
      push_cast at hcast
      exact hcast
    have hn : ‖ratComplexValue q‖≤1/16 := by nlinarith [norm_nonneg (ratComplexValue q)]
    dsimp [q] at hn
    rw [ratComplexValue_divNat] at hn
    simpa only [Nat.cast_ofNat] using hn
  have hseed : ‖ratComplexValue (w 0)-complexExpTaylor40 (ratComplexValue u/65536)‖≤2/(10:ℝ)^160 := by
    have hd := ratComplexValue_distance_le (w 0)
      (ratComplexExpTaylorScan (ratComplexDivNat u 65536) 40)
    rw [ratComplexExpTaylorScan_value, ratComplexValue_divNat] at hd
    apply hd.trans
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr hs
  have hstate : ∀ j, j<16 → ‖ratComplexValue (w j)‖≤1 :=
    fun j hj ↦ ratComplexValue_norm_le_one _ (hw ⟨j,hj⟩)
  have hstep : ∀ j, j<16 → ‖ratComplexValue (w (j+1))-(ratComplexValue (w j))^2‖≤2/(10:ℝ)^160 := by
    intro j hj
    have hd := ratComplexValue_distance_le (w (j+1)) (ratComplexMul (w j) (w j))
    rw [ratComplexValue_mul, ← pow_two] at hd
    apply hd.trans
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr (hr ⟨j,hj⟩)
  exact complexExp_scaled65536_highPrecision_error _ _ hre hnorm hseed hstate hstep

end ReciprocalXi

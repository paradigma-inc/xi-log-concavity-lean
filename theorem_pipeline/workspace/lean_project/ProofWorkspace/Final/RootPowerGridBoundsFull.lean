import ProofWorkspace.Final.RoundedEtaGridBoundsFull

set_option autoImplicit false

namespace ReciprocalXi

theorem rpow_neg_one_eightieth_pow (a : ℝ) (ha : 0 < a) :
    (a^(-(1/80):ℝ))^80 = 1/a := by
  calc
    _ = a^((-(1/80):ℝ)*(80:ℝ)) := by
      rw [Real.rpow_mul ha.le]
      simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (a^(-(1/80):ℝ)) 80).symm
    _ = a^(-1:ℝ) := by congr 1; norm_num
    _ = 1/a := by rw [Real.rpow_neg_one, one_div]

theorem rational_root80_enclosure (a l u : ℚ) (ha : 0 < a)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hlo : a*l^80 ≤ 1) (hup : 1 ≤ a*u^80) :
    (l:ℝ) ≤ (a:ℝ)^(-(1/80):ℝ) ∧ (a:ℝ)^(-(1/80):ℝ) ≤ (u:ℝ) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hlR : (0:ℝ) ≤ l := by exact_mod_cast hl
  have huR : (0:ℝ) ≤ u := by exact_mod_cast hu
  have hx := (Real.rpow_pos_of_pos haR (-(1/80):ℝ)).le
  have hx80 := rpow_neg_one_eightieth_pow (a:ℝ) haR
  have hl80 : (l:ℝ)^80 ≤ 1/(a:ℝ) := by
    apply (le_div_iff₀ haR).mpr
    have h : (a:ℝ)*(l:ℝ)^80 ≤ 1 := by exact_mod_cast hlo
    simpa only [mul_comm] using h
  have hu80 : 1/(a:ℝ) ≤ (u:ℝ)^80 := by
    apply (div_le_iff₀ haR).mpr
    have h : 1 ≤ (a:ℝ)*(u:ℝ)^80 := by exact_mod_cast hup
    simpa only [mul_comm] using h
  constructor
  · apply (pow_le_pow_iff_left₀ hlR hx (by norm_num : (80:ℕ) ≠ 0)).mp
    simpa only [hx80] using hl80
  · apply (pow_le_pow_iff_left₀ hx huR (by norm_num : (80:ℕ) ≠ 0)).mp
    simpa only [hx80] using hu80

theorem rpow_root80_grid (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (a^(-(1/80):ℝ))^(k+40) = a^(-(xiGridArgument k:ℝ)) := by
  calc
    _ = a^((-(1/80):ℝ)*(k+40)) := by
      rw [Real.rpow_mul ha.le]
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (Real.rpow_natCast (a^(-(1/80):ℝ)) (k+40)).symm
    _ = _ := by congr 1; unfold xiGridArgument; push_cast; ring

theorem ratRoot80Grid_enclosure (a l u : ℚ) (k B : ℕ) (ha : 0 < a)
    (hB : 0 < B) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : a*l^80 ≤ 1) (hup : 1 ≤ a*u^80) :
    (ratPowRoundLower l B (k+40):ℝ) ≤ (a:ℝ)^(-(xiGridArgument k:ℝ)) ∧
      (a:ℝ)^(-(xiGridArgument k:ℝ)) ≤ (ratPowRoundUpper u B (k+40):ℝ) := by
  have h := rational_root80_enclosure a l u ha hl hu hlo hup
  have he := ratPowRound_enclosure l u ((a:ℝ)^(-(1/80):ℝ)) B (k+40) hB hl h.1 h.2
  rw [rpow_root80_grid (a:ℝ) (by exact_mod_cast ha) k] at he
  exact he

end ReciprocalXi


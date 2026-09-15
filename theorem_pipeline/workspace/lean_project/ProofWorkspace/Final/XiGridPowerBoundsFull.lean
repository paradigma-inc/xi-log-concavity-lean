import ProofWorkspace.Final.RationalRoundingBoundsFull
import ProofWorkspace.Final.RationalXiBoundsFull
import ProofWorkspace.Final.RoundedSpecialFunctionBoundsFull

/-!
# Rounded geometric reuse of natural powers across the Xi grid

Only the seed and one-step power require transcendental initialization.
Every subsequent iterate is rounded outward with actual-real enclosure.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratGeoRoundLower (a b : ℚ) (B : ℕ) : ℕ → ℚ
  | 0 => ratRoundLower a B
  | k + 1 => ratRoundLower (ratGeoRoundLower a b B k * b) B

def ratGeoRoundUpper (a b : ℚ) (B : ℕ) : ℕ → ℚ
  | 0 => ratRoundUpper a B
  | k + 1 => ratRoundUpper (ratGeoRoundUpper a b B k * b) B

theorem ratGeoRoundLower_nonneg (a b : ℚ) (B k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ratGeoRoundLower a b B k := by
  induction k with
  | zero => exact ratRoundLower_nonneg a B ha
  | succ k ih => exact ratRoundLower_nonneg _ B (mul_nonneg ih hb)

theorem ratGeoRoundUpper_nonneg (a b : ℚ) (B k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ratGeoRoundUpper a b B k := by
  induction k with
  | zero => exact ratRoundUpper_nonneg a B ha
  | succ k ih => exact ratRoundUpper_nonneg _ B (mul_nonneg ih hb)

theorem ratGeoRound_enclosure (a A b C : ℚ) (x y : ℝ) (B k : ℕ)
    (hB : 0 < B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : (a : ℝ) ≤ x) (hxA : x ≤ (A : ℝ))
    (hby : (b : ℝ) ≤ y) (hyC : y ≤ (C : ℝ)) :
    (ratGeoRoundLower a b B k : ℝ) ≤ x * y ^ k ∧
      x * y ^ k ≤ (ratGeoRoundUpper A C B k : ℝ) := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hx : 0 ≤ x := haR.trans hax
  have hy : 0 ≤ y := hbR.trans hby
  have hA : 0 ≤ A := by exact_mod_cast hx.trans hxA
  have hC : 0 ≤ C := by exact_mod_cast hy.trans hyC
  induction k with
  | zero =>
    simpa only [ratGeoRoundLower, ratGeoRoundUpper, pow_zero, mul_one] using
      ratRound_interval_enclosure a A x B hB hax hxA
  | succ k ih =>
    have hl := (ratRound_real_enclosure (ratGeoRoundLower a b B k * b) B hB).1
    have hu := (ratRound_real_enclosure (ratGeoRoundUpper A C B k * C) B hB).2
    push_cast at hl hu
    have hupper : (0 : ℝ) ≤ ratGeoRoundUpper A C B k := by
      exact_mod_cast ratGeoRoundUpper_nonneg A C B k hA hC
    have hlow := mul_le_mul ih.1 hby hbR (mul_nonneg hx (pow_nonneg hy k))
    have hup := mul_le_mul ih.2 hyC hy hupper
    constructor
    · simpa only [ratGeoRoundLower, pow_succ, mul_assoc] using hl.trans hlow
    · simpa only [ratGeoRoundUpper, pow_succ, mul_assoc] using hup.trans hu

theorem ratGeoRound_mem_grid (a b : ℚ) (B k : ℕ) (hB : 0 < B) :
    ∃ l u : ℤ, (B : ℚ) * ratGeoRoundLower a b B k = l ∧
      (B : ℚ) * ratGeoRoundUpper a b B k = u := by
  cases k with
  | zero => exact ratRound_mem_grid a B hB
  | succ k =>
    obtain ⟨l, _, hl, _⟩ := ratRound_mem_grid (ratGeoRoundLower a b B k * b) B hB
    obtain ⟨_, u, _, hu⟩ := ratRound_mem_grid (ratGeoRoundUpper a b B k * b) B hB
    exact ⟨l, u, hl, hu⟩

theorem rpow_xiGridArgument (a : ℝ) (ha : 0 < a) (k : ℕ) :
    a ^ (-(xiGridArgument k : ℝ)) = a ^ (-(1 / 2 : ℝ)) *
      (a ^ (-(1 / 80 : ℝ))) ^ k := by
  rw [← Real.rpow_mul_natCast ha.le, ← Real.rpow_add ha]
  congr 1
  unfold xiGridArgument
  push_cast
  ring

theorem ratGeoRound_xiGridPower_enclosure (a : ℝ) (ha : 0 < a)
    (l₀ u₀ l₁ u₁ : ℚ) (B k : ℕ) (hB : 0 < B)
    (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁)
    (h₀ : (l₀ : ℝ) ≤ a ^ (-(1 / 2 : ℝ)) ∧ a ^ (-(1 / 2 : ℝ)) ≤ (u₀ : ℝ))
    (h₁ : (l₁ : ℝ) ≤ a ^ (-(1 / 80 : ℝ)) ∧ a ^ (-(1 / 80 : ℝ)) ≤ (u₁ : ℝ)) :
    (ratGeoRoundLower l₀ l₁ B k : ℝ) ≤ a ^ (-(xiGridArgument k : ℝ)) ∧
      a ^ (-(xiGridArgument k : ℝ)) ≤ (ratGeoRoundUpper u₀ u₁ B k : ℝ) := by
  rw [rpow_xiGridArgument a ha k]
  exact ratGeoRound_enclosure l₀ u₀ l₁ u₁ _ _ B k hB hl₀ hl₁ h₀.1 h₀.2 h₁.1 h₁.2

def ratPowerGridLower (a k L m n B : ℕ) : ℚ :=
  ratGeoRoundLower
    (max 0 (ratPowerNatRoundedLower a (-(1/2)) L m n B))
    (max 0 (ratPowerNatRoundedLower a (-(1/80)) L m n B)) B k

def ratPowerGridUpper (a k L m n B : ℕ) : ℚ :=
  ratGeoRoundUpper
    (ratPowerNatRoundedUpper a (-(1/2)) L m n B)
    (ratPowerNatRoundedUpper a (-(1/80)) L m n B) B k

/-- Only two real-power initializations are required for every grid index k. -/
theorem ratPowerGrid_enclosure (a k L m n B : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (h₀l : |ratPowerDyadicLogLower (ratPowerNatMantissa a) (-(1/2))
      (Nat.log2 a) L / m| ≤ 1)
    (h₀u : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) (-(1/2))
      (Nat.log2 a) L / m| ≤ 1)
    (h₁l : |ratPowerDyadicLogLower (ratPowerNatMantissa a) (-(1/80))
      (Nat.log2 a) L / m| ≤ 1)
    (h₁u : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) (-(1/80))
      (Nat.log2 a) L / m| ≤ 1) :
    (ratPowerGridLower a k L m n B : ℝ) ≤ (a : ℝ) ^ (-(xiGridArgument k : ℝ)) ∧
      (a : ℝ) ^ (-(xiGridArgument k : ℝ)) ≤ (ratPowerGridUpper a k L m n B : ℝ) := by
  have h₀ := ratPowerNatRounded_enclosure a (-(1/2)) L m n B ha hm hn hB h₀l h₀u
  have h₁ := ratPowerNatRounded_enclosure a (-(1/80)) L m n B ha hm hn hB h₁l h₁u
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h₀ h₁
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have h₀' : ((max 0 (ratPowerNatRoundedLower a (-(1/2)) L m n B) : ℚ) : ℝ) ≤
      (a : ℝ) ^ (-(1/2 : ℝ)) := by
    push_cast
    exact max_le (Real.rpow_nonneg haR.le _) h₀.1
  have h₁' : ((max 0 (ratPowerNatRoundedLower a (-(1/80)) L m n B) : ℚ) : ℝ) ≤
      (a : ℝ) ^ (-(1/80 : ℝ)) := by
    push_cast
    exact max_le (Real.rpow_nonneg haR.le _) h₁.1
  exact ratGeoRound_xiGridPower_enclosure (a : ℝ) haR _ _ _ _ B k hB
    (le_max_left _ _) (le_max_left _ _) ⟨h₀', h₀.2⟩ ⟨h₁', h₁.2⟩

end ReciprocalXi


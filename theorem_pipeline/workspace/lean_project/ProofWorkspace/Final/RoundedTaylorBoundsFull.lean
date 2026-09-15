import ProofWorkspace.Final.RoundedExpBoundsFull

/-!
# Fully rounded Taylor and scaled exponential bounds

Every signed Taylor term and every powering iterate is rounded outward.
A uniform proved remainder avoids exact large powers in the error term.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratExpTermRounded (q : ℚ) (B : ℕ) : ℕ → ℚ × ℚ
  | 0 => (1, 1)
  | k+1 =>
    let p := ratExpTermRounded q B k
    let c := q / (k+1)
    (ratRoundLower (min (c*p.1) (c*p.2)) B,
     ratRoundUpper (max (c*p.1) (c*p.2)) B)

theorem ratExpTermRounded_enclosure (q : ℚ) (B k : ℕ) (hB : 0 < B) :
    (ratExpTermRounded q B k).1 ≤ q^k / k.factorial ∧
      q^k / k.factorial ≤ (ratExpTermRounded q B k).2 := by
  induction k with
  | zero => norm_num [ratExpTermRounded]
  | succ k ih =>
    have he : q^(k+1) / (k+1).factorial =
        q / (k+1) * (q^k / k.factorial) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [he]
    have hl := (ratRound_enclosure
      (min ((q/(k+1))*(ratExpTermRounded q B k).1)
        ((q/(k+1))*(ratExpTermRounded q B k).2)) B hB).1
    have hu := (ratRound_enclosure
      (max ((q/(k+1))*(ratExpTermRounded q B k).1)
        ((q/(k+1))*(ratExpTermRounded q B k).2)) B hB).2
    rcases le_total (0 : ℚ) (q/(k+1)) with hc | hc
    · exact ⟨hl.trans ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left ih.1 hc)),
        ((mul_le_mul_of_nonneg_left ih.2 hc).trans (le_max_right _ _)).trans hu⟩
    · exact ⟨hl.trans ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left ih.2 hc)),
        ((mul_le_mul_of_nonpos_left ih.1 hc).trans (le_max_left _ _)).trans hu⟩

def ratExpTaylorRoundedLower (q : ℚ) (n B : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (ratExpTermRounded q B k).1

def ratExpTaylorRoundedUpper (q : ℚ) (n B : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (ratExpTermRounded q B k).2

theorem ratExpTaylorRounded_enclosure (q : ℚ) (n B : ℕ) (hB : 0 < B) :
    ratExpTaylorRoundedLower q n B ≤ ratExpTaylor q n ∧
      ratExpTaylor q n ≤ ratExpTaylorRoundedUpper q n B := by
  constructor
  · exact Finset.sum_le_sum (fun k _ => (ratExpTermRounded_enclosure q B k hB).1)
  · exact Finset.sum_le_sum (fun k _ => (ratExpTermRounded_enclosure q B k hB).2)

def ratExpUniformError (n : ℕ) : ℚ := (n+1) / (n.factorial*n)

theorem ratExpError_le_uniform (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) :
    ratExpError q n ≤ ratExpUniformError n := by
  have hp : |q|^n ≤ (1 : ℚ) := pow_le_one₀ (abs_nonneg q) hq
  unfold ratExpError ratExpUniformError
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := mul_le_mul_of_nonneg_right hp (show (0 : ℚ) ≤ n+1 by positivity)
  simpa only [one_mul] using h

theorem ratExpTaylorRounded_actual_enclosure (q : ℚ) (n B : ℕ)
    (hq : |q| ≤ 1) (hn : 0 < n) (hB : 0 < B) :
    ((ratExpTaylorRoundedLower q n B - ratExpUniformError n : ℚ) : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ ((ratExpTaylorRoundedUpper q n B + ratExpUniformError n : ℚ) : ℝ) := by
  have he := ratExp_enclosure q n hq hn
  have ht := ratExpTaylorRounded_enclosure q n B hB
  have hl : (ratExpTaylorRoundedLower q n B : ℝ) ≤ (ratExpTaylor q n : ℝ) :=
    Rat.cast_le.mpr ht.1
  have hu : (ratExpTaylor q n : ℝ) ≤ (ratExpTaylorRoundedUpper q n B : ℝ) :=
    Rat.cast_le.mpr ht.2
  have herr : (ratExpError q n : ℝ) ≤ (ratExpUniformError n : ℝ) :=
    Rat.cast_le.mpr (ratExpError_le_uniform q n hq)
  push_cast at he ⊢
  constructor <;> linarith [he.1, he.2]

def ratExpFullyRoundedLower (q : ℚ) (m n B : ℕ) : ℚ :=
  ratPowRoundLower
    (ratRoundLower (max 0 (ratExpTaylorRoundedLower (q/m) n B - ratExpUniformError n)) B) B m

def ratExpFullyRoundedUpper (q : ℚ) (m n B : ℕ) : ℚ :=
  ratPowRoundUpper
    (ratRoundUpper (ratExpTaylorRoundedUpper (q/m) n B + ratExpUniformError n) B) B m

/-- Every Taylor term and every scaled power iterate is rounded outward. -/
theorem ratExpFullyRounded_enclosure (q : ℚ) (m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B) (hq : |q/m| ≤ 1) :
    (ratExpFullyRoundedLower q m n B : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ (ratExpFullyRoundedUpper q m n B : ℝ) := by
  have h := ratExpTaylorRounded_actual_enclosure (q/m) n B hq hn hB
  have hl : ((max 0 (ratExpTaylorRoundedLower (q/m) n B - ratExpUniformError n) : ℚ) : ℝ) ≤
      Real.exp ((q/m : ℚ) : ℝ) := by
    simp only [Rat.cast_max, Rat.cast_zero]
    exact max_le (Real.exp_pos _).le h.1
  have hp := ratPowRound_enclosure
    (ratRoundLower (max 0 (ratExpTaylorRoundedLower (q/m) n B - ratExpUniformError n)) B)
    (ratRoundUpper (ratExpTaylorRoundedUpper (q/m) n B + ratExpUniformError n) B)
    (Real.exp ((q/m : ℚ) : ℝ)) B m hB
    (ratRoundLower_nonneg _ B (le_max_left _ _))
    ((ratRound_real_enclosure _ B hB).1.trans hl)
    (h.2.trans (ratRound_real_enclosure _ B hB).2)
  have he : Real.exp ((q/m : ℚ) : ℝ)^m = Real.exp (q : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    field_simp
  rw [he] at hp
  exact hp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
set_option exponentiation.threshold 512 in
theorem exp_half_fullyRounded_width :
    ratExpFullyRoundedUpper (1/2) 1 128 (10^180) -
      ratExpFullyRoundedLower (1/2) 1 128 (10^180) < (1 : ℚ)/10^160 := by
  norm_num [ratExpFullyRoundedUpper, ratExpFullyRoundedLower, ratPowRoundLower,
    ratPowRoundUpper, ratExpTaylorRoundedLower, ratExpTaylorRoundedUpper,
    ratExpTermRounded, ratExpUniformError, ratRoundLower, ratRoundUpper,
    Finset.sum_range_succ, Nat.factorial]

/-- Concrete high-precision arithmetic, with actual exponential meaning and kernel checking. -/
theorem exp_half_fullyRounded_certified :
    (ratExpFullyRoundedLower (1/2) 1 128 (10^180) : ℝ) ≤ Real.exp (1/2) ∧
    Real.exp (1/2) ≤ (ratExpFullyRoundedUpper (1/2) 1 128 (10^180) : ℝ) ∧
    ratExpFullyRoundedUpper (1/2) 1 128 (10^180) -
      ratExpFullyRoundedLower (1/2) 1 128 (10^180) < (1 : ℚ)/10^160 := by
  have h := ratExpFullyRounded_enclosure (1/2) 1 128 (10^180)
    (by norm_num) (by norm_num) (by positivity) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  exact ⟨h.1, h.2, exp_half_fullyRounded_width⟩

end ReciprocalXi

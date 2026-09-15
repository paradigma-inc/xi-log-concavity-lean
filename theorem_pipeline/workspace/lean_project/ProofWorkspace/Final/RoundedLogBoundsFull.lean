import ProofWorkspace.Final.RationalLogBoundsFull
import ProofWorkspace.Final.RationalRoundingBoundsFull
import ProofWorkspace.Final.PiBoundsFull

/-!
# Fully rounded logarithm and actual log-pi bounds

Round every odd-series term and use a proved uniform tail. The actual
logarithm is enclosed; a concrete 160-digit log-pi interval is kernel-checked.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratLogTermRounded (q : ℚ) (B : ℕ) : ℕ → ℚ × ℚ
  | 0 => (ratRoundLower (ratLogArgument q) B, ratRoundUpper (ratLogArgument q) B)
  | k+1 =>
    let p := ratLogTermRounded q B k
    let c := ratLogArgument q ^ 2 * ((2*k+1 : ℕ) : ℚ) / ((2*k+3 : ℕ) : ℚ)
    (ratRoundLower (p.1*c) B, ratRoundUpper (p.2*c) B)

theorem ratLogTermRounded_enclosure (q : ℚ) (B k : ℕ) (hB : 0 < B) :
    (ratLogTermRounded q B k).1 ≤ ratLogArgument q ^ (2*k+1) / ((2*k+1 : ℕ) : ℚ) ∧
      ratLogArgument q ^ (2*k+1) / ((2*k+1 : ℕ) : ℚ) ≤ (ratLogTermRounded q B k).2 := by
  induction k with
  | zero => simpa only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, pow_one, div_one]
      using ratRound_enclosure (ratLogArgument q) B hB
  | succ k ih =>
    have he : ratLogArgument q ^ (2*(k+1)+1) / ((2*(k+1)+1 : ℕ) : ℚ) =
        (ratLogArgument q ^ (2*k+1) / ((2*k+1 : ℕ) : ℚ)) *
          (ratLogArgument q ^ 2 * ((2*k+1 : ℕ) : ℚ) / ((2*k+3 : ℕ) : ℚ)) := by
      have hpow : 2*(k+1)+1 = (2*k+1)+2 := by omega
      rw [hpow, pow_add]
      have hd : ((2*k+1 : ℕ) : ℚ) ≠ 0 := by positivity
      push_cast at hd ⊢
      field_simp
      ring
    have hc : 0 ≤ ratLogArgument q ^ 2 * ((2*k+1 : ℕ) : ℚ) / ((2*k+3 : ℕ) : ℚ) := by positivity
    rw [he]
    have hl := (ratRound_enclosure
      ((ratLogTermRounded q B k).1 *
        (ratLogArgument q ^ 2 * ((2*k+1 : ℕ) : ℚ) / ((2*k+3 : ℕ) : ℚ))) B hB).1
    have hu := (ratRound_enclosure
      ((ratLogTermRounded q B k).2 *
        (ratLogArgument q ^ 2 * ((2*k+1 : ℕ) : ℚ) / ((2*k+3 : ℕ) : ℚ))) B hB).2
    exact ⟨hl.trans (mul_le_mul_of_nonneg_right ih.1 hc),
      (mul_le_mul_of_nonneg_right ih.2 hc).trans hu⟩

def ratLogTaylorRoundedLower (q : ℚ) (n B : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, (ratLogTermRounded q B k).1

def ratLogTaylorRoundedUpper (q : ℚ) (n B : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, (ratLogTermRounded q B k).2

theorem ratLogTaylorRounded_enclosure (q : ℚ) (n B : ℕ) (hB : 0 < B) :
    ratLogTaylorRoundedLower q n B ≤ ratLogTaylor q n ∧
      ratLogTaylor q n ≤ ratLogTaylorRoundedUpper q n B := by
  unfold ratLogTaylorRoundedLower ratLogTaylorRoundedUpper ratLogTaylor
  constructor <;> apply mul_le_mul_of_nonneg_left _ (by norm_num) <;>
    apply Finset.sum_le_sum <;> intro k hk
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (ratLogTermRounded_enclosure q B k hB).1
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (ratLogTermRounded_enclosure q B k hB).2

def ratLogUniformError (r : ℚ) (n : ℕ) : ℚ := 2*r^(2*n+1)/(1-r^2)

theorem ratLogError_le_uniform (q r : ℚ) (n : ℕ)
    (hqr : |ratLogArgument q| ≤ r) (hr : r < 1) :
    ratLogError q n ≤ ratLogUniformError r n := by
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hqr
  have hsq := pow_le_pow_left₀ (abs_nonneg (ratLogArgument q)) hqr 2
  rw [sq_abs] at hsq
  have hd : 0 < 1-r^2 := by nlinarith
  have hden : 1-r^2 ≤ 1-ratLogArgument q^2 := by linarith
  have hp := pow_le_pow_left₀ (abs_nonneg (ratLogArgument q)) hqr (2*n+1)
  unfold ratLogError ratLogUniformError
  calc
    _ ≤ 2*r^(2*n+1)/(1-ratLogArgument q^2) :=
      div_le_div_of_nonneg_right (by linarith) (hd.le.trans hden)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd hden

def ratLogFullyRoundedLower (q r : ℚ) (n B : ℕ) : ℚ :=
  ratRoundLower (ratLogTaylorRoundedLower q n B - ratLogUniformError r n) B

def ratLogFullyRoundedUpper (q r : ℚ) (n B : ℕ) : ℚ :=
  ratRoundUpper (ratLogTaylorRoundedUpper q n B + ratLogUniformError r n) B

theorem ratLogFullyRounded_enclosure (q r : ℚ) (n B : ℕ)
    (hq : 0 < q) (hB : 0 < B) (hqr : |ratLogArgument q| ≤ r) (hr : r < 1) :
    (ratLogFullyRoundedLower q r n B : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (ratLogFullyRoundedUpper q r n B : ℝ) := by
  have he := ratLog_enclosure q n hq
  have ht := ratLogTaylorRounded_enclosure q n B hB
  have hl : (ratLogTaylorRoundedLower q n B : ℝ) ≤ (ratLogTaylor q n : ℝ) := Rat.cast_le.mpr ht.1
  have hu : (ratLogTaylor q n : ℝ) ≤ (ratLogTaylorRoundedUpper q n B : ℝ) := Rat.cast_le.mpr ht.2
  have herr : (ratLogError q n : ℝ) ≤ (ratLogUniformError r n : ℝ) :=
    Rat.cast_le.mpr (ratLogError_le_uniform q r n hqr hr)
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast at he ⊢
    linarith [he.1]
  · push_cast at he ⊢
    linarith [he.2]

theorem ratLogFullyRounded_interval_enclosure (a b r : ℚ) (x : ℝ) (n B : ℕ)
    (ha : 0 < a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) (hB : 0 < B)
    (har : |ratLogArgument a| ≤ r) (hbr : |ratLogArgument b| ≤ r) (hr : r < 1) :
    (ratLogFullyRoundedLower a r n B : ℝ) ≤ Real.log x ∧
      Real.log x ≤ (ratLogFullyRoundedUpper b r n B : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx : 0 < x := haR.trans_le hax
  have hb : 0 < b := by exact_mod_cast hx.trans_le hxb
  exact ⟨(ratLogFullyRounded_enclosure a r n B ha hB har hr).1.trans
      (Real.log_le_log haR hax),
    (Real.log_le_log hx hxb).trans (ratLogFullyRounded_enclosure b r n B hb hB hbr hr).2⟩

theorem ratLogArgument_bound_on_one_four (q : ℚ) (h₁ : 1 ≤ q) (h₄ : q ≤ 4) :
    |ratLogArgument q| ≤ 3/5 := by
  have hd : 0 < q+1 := by linarith
  have ht : 0 ≤ ratLogArgument q := div_nonneg (by linarith) hd.le
  rw [abs_of_nonneg ht]
  exact (div_le_iff₀ hd).mpr (by linarith)

theorem machinPi_endpoints_one_four :
    (1 ≤ machinPiLower ∧ machinPiLower ≤ 4) ∧
      (1 ≤ machinPiUpper ∧ machinPiUpper ≤ 4) := by
  have hw : (machinPiUpper : ℝ) - (machinPiLower : ℝ) < 1/2 := by
    have h : machinPiUpper - machinPiLower < 1/2 := machinPi_width_lt.trans (by norm_num)
    have hc := (Rat.cast_lt (K := ℝ)).mpr h
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hl := machinPi_enclosure.1
  have hu := machinPi_enclosure.2
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_d2
  have h₁ : (1 : ℝ) ≤ machinPiLower := by linarith
  have h₂ : (machinPiLower : ℝ) ≤ 4 := by linarith
  have h₃ : (1 : ℝ) ≤ machinPiUpper := by linarith
  have h₄ : (machinPiUpper : ℝ) ≤ 4 := by linarith
  exact_mod_cast And.intro (And.intro h₁ h₂) (And.intro h₃ h₄)

def ratPiLogFullyRoundedLower (n B : ℕ) : ℚ :=
  ratLogFullyRoundedLower machinPiLower (3/5) n B

def ratPiLogFullyRoundedUpper (n B : ℕ) : ℚ :=
  ratLogFullyRoundedUpper machinPiUpper (3/5) n B

theorem ratPiLogFullyRounded_enclosure (n B : ℕ) (hB : 0 < B) :
    (ratPiLogFullyRoundedLower n B : ℝ) ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ (ratPiLogFullyRoundedUpper n B : ℝ) := by
  have h := machinPi_endpoints_one_four
  exact ratLogFullyRounded_interval_enclosure machinPiLower machinPiUpper (3/5) Real.pi n B
    machinPiLower_pos machinPi_enclosure.1 machinPi_enclosure.2 hB
    (ratLogArgument_bound_on_one_four _ h.1.1 h.1.2)
    (ratLogArgument_bound_on_one_four _ h.2.1 h.2.2) (by norm_num)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 15000000 in
set_option exponentiation.threshold 1024 in
theorem piLogFullyRounded_width :
    ratPiLogFullyRoundedUpper 400 (10^180) -
      ratPiLogFullyRoundedLower 400 (10^180) < (1 : ℚ)/10^160 := by
  norm_num [ratPiLogFullyRoundedLower, ratPiLogFullyRoundedUpper,
    ratLogFullyRoundedLower, ratLogFullyRoundedUpper,
    ratLogTaylorRoundedLower, ratLogTaylorRoundedUpper, ratLogTermRounded,
    ratLogUniformError, ratLogArgument, ratRoundLower, ratRoundUpper,
    machinPiLower, machinPiUpper, machinPiMidpoint, machinPiRadius,
    ratArctanTaylor, ratArctanError, Finset.sum_range_succ]


/-- A concrete actual log-pi enclosure, with all finite arithmetic checked by the kernel. -/
theorem piLogFullyRounded_certified :
    (ratPiLogFullyRoundedLower 400 (10^180) : ℝ) ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (ratPiLogFullyRoundedUpper 400 (10^180) : ℝ) ∧
    ratPiLogFullyRoundedUpper 400 (10^180) -
      ratPiLogFullyRoundedLower 400 (10^180) < (1 : ℚ)/10^160 := by
  have h := ratPiLogFullyRounded_enclosure 400 (10^180) (by positivity)
  exact ⟨h.1, h.2, piLogFullyRounded_width⟩

end ReciprocalXi


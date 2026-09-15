import ProofWorkspace.Final.XiGridPowerBoundsFull

set_option autoImplicit false

namespace ReciprocalXi

def ratEtaGridRoundedTermLower (N k j L m n B : ℕ) : ℚ :=
  ratRoundLower
    (min (ratEtaCoefficient N j * ratPowerGridLower (j+1) k L m n B)
      (ratEtaCoefficient N j * ratPowerGridUpper (j+1) k L m n B)) B

def ratEtaGridRoundedTermUpper (N k j L m n B : ℕ) : ℚ :=
  ratRoundUpper
    (max (ratEtaCoefficient N j * ratPowerGridLower (j+1) k L m n B)
      (ratEtaCoefficient N j * ratPowerGridUpper (j+1) k L m n B)) B

def ratEtaGridRoundedLower (N k L m n B : ℕ) : ℚ :=
  ratRoundLower (∑ j ∈ Finset.range N, ratEtaGridRoundedTermLower N k j L m n B) B

def ratEtaGridRoundedUpper (N k L m n B : ℕ) : ℚ :=
  ratRoundUpper ((∑ j ∈ Finset.range N, ratEtaGridRoundedTermUpper N k j L m n B) +
    1 / 2^N) B

/-- Initial power checks do not depend on the retained-node index. -/
structure GridPowerChecks (a L m : ℕ) : Prop where
  half_lower : |ratPowerDyadicLogLower (ratPowerNatMantissa a) (-(1/2))
    (Nat.log2 a) L / m| ≤ 1
  half_upper : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) (-(1/2))
    (Nat.log2 a) L / m| ≤ 1
  step_lower : |ratPowerDyadicLogLower (ratPowerNatMantissa a) (-(1/80))
    (Nat.log2 a) L / m| ≤ 1
  step_upper : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) (-(1/80))
    (Nat.log2 a) L / m| ≤ 1

theorem ratEtaGridRoundedTerm_enclosure (N k j L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B) (hc : GridPowerChecks (j+1) L m) :
    (ratEtaGridRoundedTermLower N k j L m n B : ℝ) ≤
      (-1 : ℝ)^j * etaEulerWeight N j / ((j : ℝ)+1) ^ (xiGridArgument k : ℝ) ∧
    (-1 : ℝ)^j * etaEulerWeight N j / ((j : ℝ)+1) ^ (xiGridArgument k : ℝ) ≤
      (ratEtaGridRoundedTermUpper N k j L m n B : ℝ) := by
  have hp := ratPowerGrid_enclosure (j+1) k L m n B (by omega) hm hn hB
    hc.half_lower hc.half_upper hc.step_lower hc.step_upper
  push_cast at hp
  have he : (-1 : ℝ)^j * etaEulerWeight N j / ((j : ℝ)+1) ^ (xiGridArgument k : ℝ) =
      (ratEtaCoefficient N j : ℝ) * (((j : ℝ)+1) ^ (-(xiGridArgument k : ℝ))) := by
    rw [ratEtaCoefficient_cast, Real.rpow_neg (by positivity)]
    rfl
  rw [he]
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast
    rcases le_total (0 : ℝ) (ratEtaCoefficient N j : ℝ) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp.1 h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hp.2 h)
  · push_cast
    rcases le_total (0 : ℝ) (ratEtaCoefficient N j : ℝ) with h | h
    · exact (mul_le_mul_of_nonneg_left hp.2 h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hp.1 h).trans (le_max_left _ _)

/-- Rounded grid reuse bounds the actual eta integral, retaining its directed tail. -/
theorem ratEtaGridRounded_enclosure (N k L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hc : ∀ j ∈ Finset.range N, GridPowerChecks (j+1) L m) :
    (ratEtaGridRoundedLower N k L m n B : ℝ) ≤ etaIntegral (xiGridArgument k : ℝ) ∧
      etaIntegral (xiGridArgument k : ℝ) ≤ (ratEtaGridRoundedUpper N k L m n B : ℝ) := by
  have hs : 0 < (xiGridArgument k : ℝ) := by exact_mod_cast xiGridArgument_pos k
  have he := etaIntegral_euler_error_bounds N (xiGridArgument k : ℝ) hs
  have hl : ((∑ j ∈ Finset.range N, ratEtaGridRoundedTermLower N k j L m n B : ℚ) : ℝ) ≤
      etaEulerApprox N (xiGridArgument k : ℝ) := by
    unfold etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaGridRoundedTerm_enclosure N k j L m n B hm hn hB (hc j hj)).1
  have hu : etaEulerApprox N (xiGridArgument k : ℝ) ≤
      ((∑ j ∈ Finset.range N, ratEtaGridRoundedTermUpper N k j L m n B : ℚ) : ℝ) := by
    unfold etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaGridRoundedTerm_enclosure N k j L m n B hm hn hB (hc j hj)).2
  apply ratRound_interval_enclosure _ _ _ B hB
  · linarith [he.1]
  · push_cast
    push_cast at hu
    linarith [he.2]

theorem ratEtaGridRounded_mem_grid (N k L m n B : ℕ) (hB : 0 < B) :
    ∃ l u : ℤ, (B : ℚ) * ratEtaGridRoundedLower N k L m n B = l ∧
      (B : ℚ) * ratEtaGridRoundedUpper N k L m n B = u := by
  obtain ⟨l, _, hl, _⟩ := ratRound_mem_grid
    (∑ j ∈ Finset.range N, ratEtaGridRoundedTermLower N k j L m n B) B hB
  obtain ⟨_, u, _, hu⟩ := ratRound_mem_grid
    ((∑ j ∈ Finset.range N, ratEtaGridRoundedTermUpper N k j L m n B) + 1/2^N) B hB
  exact ⟨l, u, hl, hu⟩

end ReciprocalXi


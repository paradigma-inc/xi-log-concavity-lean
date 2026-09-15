import ProofWorkspace.Final.RetainedRootEvaluatorFull

set_option autoImplicit false
namespace ReciprocalXi

theorem ratRoundUpper_mono (a b : ℚ) (B : ℕ) (hab : a ≤ b) :
    ratRoundUpper a B ≤ ratRoundUpper b B := by
  unfold ratRoundUpper
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg B)
  exact_mod_cast Int.ceil_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg B))

theorem ratPowRoundUpper_round_exact (a : ℚ) (B n : ℕ) (hB : 0 < B) :
    ratRoundUpper (ratPowRoundUpper a B n) B = ratPowRoundUpper a B n := by
  obtain ⟨l,u,hl,hu⟩ := ratPowRound_mem_grid a B n hB
  have he : ratPowRoundUpper a B n = (u:ℚ)/B := by
    apply (eq_div_iff (by exact_mod_cast ne_of_gt hB)).mpr
    simpa only [mul_comm] using hu
  rw [he]
  exact (ratRound_grid_exact u B hB).2

theorem ratPowRoundLower_antitone (a : ℚ) (B : ℕ) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Antitone (ratPowRoundLower a B) := by
  apply antitone_nat_of_succ_le
  intro n
  have h0 := ratPowRoundLower_nonneg a B n ha
  calc
    ratPowRoundLower a B (n+1) ≤ ratPowRoundLower a B n * a :=
      (ratRound_enclosure _ B hB).1
    _ ≤ ratPowRoundLower a B n := mul_le_of_le_one_right h0 ha1

theorem ratPowRoundUpper_antitone (a : ℚ) (B : ℕ) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Antitone (ratPowRoundUpper a B) := by
  apply antitone_nat_of_succ_le
  intro n
  have h0 := ratPowRoundUpper_nonneg a B n ha
  calc
    ratPowRoundUpper a B (n+1) ≤ ratRoundUpper (ratPowRoundUpper a B n) B :=
      ratRoundUpper_mono _ _ B (mul_le_of_le_one_right h0 ha1)
    _ = ratPowRoundUpper a B n := ratPowRoundUpper_round_exact a B n hB

set_option maxRecDepth 32768 in
theorem retainedTwo_roots_le_one : rootLowerFor 2 ≤ 1 ∧ rootUpperFor 2 ≤ 1 := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem retainedTwo_denominator_nearest_checks :
    1/2 < retainedTwoLower 39 ∧ retainedTwoUpper 41 < 1/2 := by
  decide +kernel

theorem retainedRoot_denominator_pos (k : ℕ) (hk : k ≠ 40) :
    0 < ratRootDenominatorLower (xiGridArgument k) (retainedTwoLower k) (retainedTwoUpper k) := by
  have hc := rootPowerGridBounds 2 (by norm_num) (by norm_num)
  have hlmono := ratPowRoundLower_antitone (rootLowerFor 2) (10^180)
    (by norm_num) hc.1 retainedTwo_roots_le_one.1
  have humono := ratPowRoundUpper_antitone (rootUpperFor 2) (10^180)
    (by norm_num) hc.2.1 retainedTwo_roots_le_one.2
  by_cases hkl : k < 40
  · have hs : xiGridArgument k < 1 := by
      unfold xiGridArgument
      have h : (k:ℚ) < 40 := by exact_mod_cast hkl
      linarith
    unfold ratRootDenominatorLower
    rw [if_pos hs]
    have h := hlmono (show k+40 ≤ 39+40 by omega)
    change retainedTwoLower 39 ≤ retainedTwoLower k at h
    linarith [retainedTwo_denominator_nearest_checks.1]
  · have hs : ¬xiGridArgument k < 1 := by
      unfold xiGridArgument
      have h : (40:ℚ) ≤ k := by exact_mod_cast (Nat.le_of_not_gt hkl)
      linarith
    unfold ratRootDenominatorLower
    rw [if_neg hs]
    have h := humono (show 41+40 ≤ k+40 by omega)
    change retainedTwoUpper k ≤ retainedTwoUpper 41 at h
    linarith [retainedTwo_denominator_nearest_checks.2]

end ReciprocalXi

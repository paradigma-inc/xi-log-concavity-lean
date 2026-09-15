import ProofWorkspace.Final.RetainedRootEvaluatorFull

set_option autoImplicit false
namespace ReciprocalXi

def sourcePowerPairStep (a b : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (ratRoundLower (p.1*a) (10^180), ratRoundUpper (p.2*b) (10^180))

theorem retainedPiPair_succ (k : ℕ) :
    (retainedPiLower (k+1), retainedPiUpper (k+1)) =
      sourcePowerPairStep sourcePiRootLower sourcePiRootUpper
        (retainedPiLower k, retainedPiUpper k) := by
  simp only [retainedPiLower, retainedPiUpper, ratPowRoundLower,
    ratPowRoundUpper, sourcePowerPairStep]

theorem retainedTwoPair_succ (k : ℕ) :
    (retainedTwoLower (k+1), retainedTwoUpper (k+1)) =
      sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2)
        (retainedTwoLower k, retainedTwoUpper k) := by
  simp only [retainedTwoLower, retainedTwoUpper, ratPowRoundLower,
    ratPowRoundUpper, sourcePowerPairStep]

theorem sourcePowerTable_sound (f : ℕ → ℚ × ℚ) (step : (ℚ × ℚ) → ℚ × ℚ)
    (hstep : ∀ k, f (k+1) = step (f k)) (start count : ℕ) (data : List (ℚ × ℚ))
    (hfirst : f start = data.getD 0 (0,0))
    (hnext : ∀ k, k+1 < count →
      data.getD (k+1) (0,0) = step (data.getD k (0,0)))
    (k : ℕ) (hk : k < count) : f (start+k) = data.getD k (0,0) := by
  induction k with
  | zero => simpa only [Nat.add_zero] using hfirst
  | succ k ih =>
    rw [Nat.add_succ, hstep, ih (by omega)]
    exact (hnext k hk).symm

end ReciprocalXi

import ProofWorkspace.Final.RoundedTaylorBoundsFull
import ProofWorkspace.Final.RoundedLogBoundsFull

/-! Exact single-pass accumulation of the accepted rounded exponential/logarithm terms. -/

set_option autoImplicit false

namespace ReciprocalXi

/-- Accumulate a rounded recurrence without recomputing earlier terms. -/
def ratPairSumLoop (step : ℕ → ℚ × ℚ → ℚ × ℚ) :
    ℕ → ℕ → ℚ × ℚ → ℚ × ℚ → ℚ × ℚ
  | 0, _, _, a => a
  | n+1, j, t, a => ratPairSumLoop step n (j+1) (step j t) (a+t)

theorem ratPairSumLoop_eq (step : ℕ → ℚ × ℚ → ℚ × ℚ)
    (t : ℕ → ℚ × ℚ) (ht : ∀ j, step j (t j) = t (j+1))
    (n j : ℕ) (a : ℚ × ℚ) :
    ratPairSumLoop step n j (t j) a = a + ∑ i ∈ Finset.range n, t (j+i) := by
  induction n generalizing j a with
  | zero => simp [ratPairSumLoop]
  | succ n ih =>
    rw [ratPairSumLoop, ht, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_left_comm, Nat.add_comm]
    abel

def ratExpTaylorScan (q : ℚ) (n B : ℕ) : ℚ × ℚ :=
  ratPairSumLoop (fun j p =>
    let c := q/(j+1)
    (ratRoundLower (min (c*p.1) (c*p.2)) B,
     ratRoundUpper (max (c*p.1) (c*p.2)) B)) n 0 (1,1) (0,0)

theorem ratExpTaylorScan_eq (q : ℚ) (n B : ℕ) :
    ratExpTaylorScan q n B =
      (ratExpTaylorRoundedLower q n B, ratExpTaylorRoundedUpper q n B) := by
  have h := ratPairSumLoop_eq
    (fun j p =>
      let c := q/(j+1)
      (ratRoundLower (min (c*p.1) (c*p.2)) B,
       ratRoundUpper (max (c*p.1) (c*p.2)) B))
    (ratExpTermRounded q B) (fun _ => rfl) n 0 (0,0)
  have hz : ((0,0) : ℚ × ℚ) = 0 := rfl
  rw [hz, zero_add] at h
  have he : ratExpTaylorScan q n B = ∑ i ∈ Finset.range n, ratExpTermRounded q B i := by
    simpa only [ratExpTaylorScan, ratExpTermRounded, Nat.zero_add, hz] using h
  rw [he]
  apply Prod.ext
  · simp only [ratExpTaylorRoundedLower, Prod.fst_sum]
  · simp only [ratExpTaylorRoundedUpper, Prod.snd_sum]

def ratLogTaylorScan (q : ℚ) (n B : ℕ) : ℚ × ℚ :=
  let sq := ratLogArgument q ^ 2
  let p := ratPairSumLoop (fun j p =>
    let c := sq * ((2*j+1:ℕ):ℚ) / ((2*j+3:ℕ):ℚ)
    (ratRoundLower (p.1*c) B, ratRoundUpper (p.2*c) B)) n 0
    (ratRoundLower (ratLogArgument q) B, ratRoundUpper (ratLogArgument q) B) (0,0)
  (2*p.1,2*p.2)

theorem ratLogTaylorScan_eq (q : ℚ) (n B : ℕ) :
    ratLogTaylorScan q n B =
      (ratLogTaylorRoundedLower q n B, ratLogTaylorRoundedUpper q n B) := by
  have h := ratPairSumLoop_eq
    (fun j p =>
      let c := ratLogArgument q ^ 2 * ((2*j+1:ℕ):ℚ) / ((2*j+3:ℕ):ℚ)
      (ratRoundLower (p.1*c) B, ratRoundUpper (p.2*c) B))
    (ratLogTermRounded q B) (fun _ => rfl) n 0 (0,0)
  unfold ratLogTaylorScan
  change (2*(ratPairSumLoop _ n 0 (ratLogTermRounded q B 0) (0,0)).1,
    2*(ratPairSumLoop _ n 0 (ratLogTermRounded q B 0) (0,0)).2) = _
  rw [h]
  simp [ratLogTaylorRoundedLower, ratLogTaylorRoundedUpper, Prod.fst_sum, Prod.snd_sum]

theorem ratExpTaylorScan_lower (q : ℚ) (n B : ℕ) :
    (ratExpTaylorScan q n B).1 = ratExpTaylorRoundedLower q n B := by
  rw [ratExpTaylorScan_eq]

theorem ratExpTaylorScan_upper (q : ℚ) (n B : ℕ) :
    (ratExpTaylorScan q n B).2 = ratExpTaylorRoundedUpper q n B := by
  rw [ratExpTaylorScan_eq]

theorem ratLogTaylorScan_lower (q : ℚ) (n B : ℕ) :
    (ratLogTaylorScan q n B).1 = ratLogTaylorRoundedLower q n B := by
  rw [ratLogTaylorScan_eq]

theorem ratLogTaylorScan_upper (q : ℚ) (n B : ℕ) :
    (ratLogTaylorScan q n B).2 = ratLogTaylorRoundedUpper q n B := by
  rw [ratLogTaylorScan_eq]

end ReciprocalXi


import ProofWorkspace.Final.RoundedEtaGridBoundsFull
import ProofWorkspace.Final.RoundedGammaLogBoundsFull

/-! Exact linear binomial-tail tabulation and identical rounded eta/zeta sums. -/

set_option autoImplicit false

namespace ReciprocalXi

def ratBinomialTail (M j : ℕ) : ℚ :=
  ∑ n ∈ (Finset.range (M + 1)).filter (fun n => j ≤ n), (M.choose n : ℚ)

theorem ratBinomialTail_zero (M : ℕ) : ratBinomialTail M 0 = (2 : ℚ)^M := by
  unfold ratBinomialTail
  simp only [Nat.zero_le, Finset.filter_true]
  exact_mod_cast Nat.sum_range_choose M

theorem ratBinomialTail_succ (M j : ℕ) :
    ratBinomialTail M (j+1) = ratBinomialTail M j - (M.choose j : ℚ) := by
  have hterm (n : ℕ) :
      (if j ≤ n then (M.choose n : ℚ) else 0) =
        (if n = j then (M.choose n : ℚ) else 0) +
        (if j+1 ≤ n then (M.choose n : ℚ) else 0) := by
    by_cases he : n = j
    · subst n; simp
    · by_cases hl : j < n
      · simp [he, Nat.le_of_lt hl, Nat.succ_le_iff.mpr hl]
      · have hn : n < j := by omega
        simp [he, show ¬j ≤ n by omega, show ¬j+1 ≤ n by omega]
  have heq : (∑ n ∈ Finset.range (M+1), if n = j then (M.choose n : ℚ) else 0) =
      (M.choose j : ℚ) := by
    rw [Finset.sum_ite_eq']
    by_cases hj : j < M+1
    · simp [Finset.mem_range, hj]
    · have hz : M.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [Finset.mem_range, hj, hz]
  unfold ratBinomialTail
  simp only [Finset.sum_filter]
  conv_rhs => arg 1; arg 2; ext n; rw [hterm]
  rw [Finset.sum_add_distrib, heq]
  ring

theorem ratEtaEulerWeight_eq_tail (M j : ℕ) :
    ratEtaEulerWeight M j = ratBinomialTail M (j+1) / (2 : ℚ)^M := by
  unfold ratEtaEulerWeight ratBinomialTail
  simp only [Nat.succ_le_iff]

theorem ratChoose_succ (M j : ℕ) :
    (M.choose (j+1) : ℚ) = (M.choose j : ℚ) * ((M-j : ℕ) : ℚ) / (j+1) := by
  have h := Nat.choose_succ_right_eq M j
  have hc : (M.choose (j+1) : ℚ) * (j+1) = (M.choose j : ℚ) * ((M-j : ℕ) : ℚ) := by
    exact_mod_cast h
  exact (eq_div_iff (by positivity : (j:ℚ)+1 ≠ 0)).mpr hc

/-- Carry the next binomial coefficient and the remaining tail. -/
def ratEtaWeightTableAux (M : ℕ) : ℕ → ℕ → ℚ → ℚ → List ℚ
  | 0, _, _, _ => []
  | n+1, j, c, t =>
    let t' := t-c
    t'/(2:ℚ)^M :: ratEtaWeightTableAux M n (j+1) (c*((M-j:ℕ):ℚ)/(j+1)) t'

theorem ratEtaWeightTableAux_eq (M n j : ℕ) :
    ratEtaWeightTableAux M n j (M.choose j) (ratBinomialTail M j) =
      (List.range' j n).map (ratEtaEulerWeight M) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [ratEtaWeightTableAux, ←ratBinomialTail_succ, ←ratChoose_succ, ih]
    rw [List.range'_succ, List.map_cons, ratEtaEulerWeight_eq_tail]

def ratEtaWeightTable (M : ℕ) : List ℚ :=
  ratEtaWeightTableAux M M 0 1 ((2:ℚ)^M)

theorem ratEtaWeightTable_eq (M : ℕ) :
    ratEtaWeightTable M = (List.range M).map (ratEtaEulerWeight M) := by
  have h := ratEtaWeightTableAux_eq M M 0
  simpa [ratEtaWeightTable, ratBinomialTail_zero, List.range_eq_range'] using h

theorem ratEtaWeightTable_length (M : ℕ) : (ratEtaWeightTable M).length = M := by
  simp [ratEtaWeightTable_eq]

theorem ratEtaWeightTable_getElem (M j : ℕ) (hj : j < (ratEtaWeightTable M).length) :
    (ratEtaWeightTable M)[j] = ratEtaEulerWeight M j := by
  simp [ratEtaWeightTable_eq]

theorem ratEtaWeightTable_getD (M j : ℕ) (hj : j < M) :
    (ratEtaWeightTable M)[j]?.getD 0 = ratEtaEulerWeight M j := by
  simp [ratEtaWeightTable_eq, hj]

theorem ratEtaWeightTable_mapIdx (M : ℕ) (f : ℕ → ℚ → ℚ) :
    (ratEtaWeightTable M).mapIdx f =
      (List.range M).map (fun j => f j (ratEtaEulerWeight M j)) := by
  apply List.ext_getElem
  · simp [ratEtaWeightTable_length]
  · intro j hj hj'
    simp [ratEtaWeightTable_eq]

theorem ratEtaWeightTable_sum_mapIdx (M : ℕ) (f : ℕ → ℚ → ℚ) :
    ((ratEtaWeightTable M).mapIdx f).sum =
      ∑ j ∈ Finset.range M, f j (ratEtaEulerWeight M j) := by
  rw [ratEtaWeightTable_mapIdx]
  have hs (n : ℕ) : ((List.range n).map (fun j => f j (ratEtaEulerWeight M j))).sum =
      ∑ j ∈ Finset.range n, f j (ratEtaEulerWeight M j) := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  exact hs M

def ratEtaIntegerTableLower (M k B : ℕ) : ℚ :=
  ((ratEtaWeightTable M).mapIdx (fun j w =>
    ratRoundLower ((-1:ℚ)^j * w / ((j:ℚ)+1)^k) B)).sum

def ratEtaIntegerTableUpper (M k B : ℕ) : ℚ :=
  ((ratEtaWeightTable M).mapIdx (fun j w =>
    ratRoundUpper ((-1:ℚ)^j * w / ((j:ℚ)+1)^k) B)).sum

theorem ratEtaIntegerTableLower_eq (M k B : ℕ) :
    ratEtaIntegerTableLower M k B = ratEtaIntegerRoundedLower M k B := by
  exact ratEtaWeightTable_sum_mapIdx M _

theorem ratEtaIntegerTableUpper_eq (M k B : ℕ) :
    ratEtaIntegerTableUpper M k B = ratEtaIntegerRoundedUpper M k B := by
  exact ratEtaWeightTable_sum_mapIdx M _

def ratEtaGridTableLower (N k L m n B : ℕ) : ℚ :=
  ratRoundLower ((ratEtaWeightTable N).mapIdx (fun j w =>
    let c := (-1:ℚ)^j*w
    ratRoundLower (min (c*ratPowerGridLower (j+1) k L m n B)
      (c*ratPowerGridUpper (j+1) k L m n B)) B)).sum B

def ratEtaGridTableUpper (N k L m n B : ℕ) : ℚ :=
  ratRoundUpper (((ratEtaWeightTable N).mapIdx (fun j w =>
    let c := (-1:ℚ)^j*w
    ratRoundUpper (max (c*ratPowerGridLower (j+1) k L m n B)
      (c*ratPowerGridUpper (j+1) k L m n B)) B)).sum + 1/2^N) B

theorem ratEtaGridTableLower_eq (N k L m n B : ℕ) :
    ratEtaGridTableLower N k L m n B = ratEtaGridRoundedLower N k L m n B := by
  unfold ratEtaGridTableLower ratEtaGridRoundedLower
  rw [ratEtaWeightTable_sum_mapIdx]
  rfl

theorem ratEtaGridTableUpper_eq (N k L m n B : ℕ) :
    ratEtaGridTableUpper N k L m n B = ratEtaGridRoundedUpper N k L m n B := by
  unfold ratEtaGridTableUpper ratEtaGridRoundedUpper
  rw [ratEtaWeightTable_sum_mapIdx]
  rfl

end ReciprocalXi


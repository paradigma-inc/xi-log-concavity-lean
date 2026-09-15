import ProofWorkspace.Final.RootPowerGridBoundsFull
import ProofWorkspace.Final.EtaWeightTableFull

/-! Actual eta-grid intervals from rational eightieth-root certificates, with
outward-rounded signed Euler terms and the unchanged directed remainder. -/

set_option autoImplicit false

namespace ReciprocalXi

def ratEtaRootGridTermLower (N k j B : ℕ) (l u : ℚ) : ℚ :=
  ratRoundLower
    (min (ratEtaCoefficient N j * ratPowRoundLower l B (k+40))
      (ratEtaCoefficient N j * ratPowRoundUpper u B (k+40))) B

def ratEtaRootGridTermUpper (N k j B : ℕ) (l u : ℚ) : ℚ :=
  ratRoundUpper
    (max (ratEtaCoefficient N j * ratPowRoundLower l B (k+40))
      (ratEtaCoefficient N j * ratPowRoundUpper u B (k+40))) B

def ratEtaRootGridLower (N k B : ℕ) (lo hi : ℕ → ℚ) : ℚ :=
  ratRoundLower (∑ j ∈ Finset.range N,
    ratEtaRootGridTermLower N k j B (lo (j+1)) (hi (j+1))) B

def ratEtaRootGridUpper (N k B : ℕ) (lo hi : ℕ → ℚ) : ℚ :=
  ratRoundUpper ((∑ j ∈ Finset.range N,
    ratEtaRootGridTermUpper N k j B (lo (j+1)) (hi (j+1))) + 1/2^N) B

theorem ratEtaRootGridTerm_enclosure (N k j B : ℕ) (l u : ℚ)
    (hB : 0 < B) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : ((j:ℚ)+1)*l^80 ≤ 1) (hup : 1 ≤ ((j:ℚ)+1)*u^80) :
    (ratEtaRootGridTermLower N k j B l u : ℝ) ≤
      (-1:ℝ)^j * etaEulerWeight N j / ((j:ℝ)+1)^(xiGridArgument k:ℝ) ∧
    (-1:ℝ)^j * etaEulerWeight N j / ((j:ℝ)+1)^(xiGridArgument k:ℝ) ≤
      (ratEtaRootGridTermUpper N k j B l u : ℝ) := by
  have hp := ratRoot80Grid_enclosure ((j:ℚ)+1) l u k B
    (by positivity) hB hl hu hlo hup
  push_cast at hp
  have he : (-1:ℝ)^j * etaEulerWeight N j / ((j:ℝ)+1)^(xiGridArgument k:ℝ) =
      (ratEtaCoefficient N j:ℝ) * (((j:ℝ)+1)^(-(xiGridArgument k:ℝ))) := by
    rw [ratEtaCoefficient_cast, Real.rpow_neg (by positivity)]
    rfl
  rw [he]
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast
    rcases le_total (0:ℝ) (ratEtaCoefficient N j:ℝ) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp.1 h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hp.2 h)
  · push_cast
    rcases le_total (0:ℝ) (ratEtaCoefficient N j:ℝ) with h | h
    · exact (mul_le_mul_of_nonneg_left hp.2 h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hp.1 h).trans (le_max_left _ _)

/-- Root certificates for the integer bases give actual eta bounds at every grid node. -/
theorem ratEtaRootGrid_enclosure (N k B : ℕ) (lo hi : ℕ → ℚ)
    (hB : 0 < B)
    (hc : ∀ j ∈ Finset.range N,
      0 ≤ lo (j+1) ∧ 0 ≤ hi (j+1) ∧
      ((j:ℚ)+1)*(lo (j+1))^80 ≤ 1 ∧ 1 ≤ ((j:ℚ)+1)*(hi (j+1))^80) :
    (ratEtaRootGridLower N k B lo hi : ℝ) ≤ etaIntegral (xiGridArgument k:ℝ) ∧
      etaIntegral (xiGridArgument k:ℝ) ≤ (ratEtaRootGridUpper N k B lo hi : ℝ) := by
  have hs : 0 < (xiGridArgument k:ℝ) := by exact_mod_cast xiGridArgument_pos k
  have he := etaIntegral_euler_error_bounds N (xiGridArgument k:ℝ) hs
  have ht (j : ℕ) (hj : j ∈ Finset.range N) :=
    ratEtaRootGridTerm_enclosure N k j B (lo (j+1)) (hi (j+1)) hB
      (hc j hj).1 (hc j hj).2.1 (hc j hj).2.2.1 (hc j hj).2.2.2
  have hl : ((∑ j ∈ Finset.range N,
      ratEtaRootGridTermLower N k j B (lo (j+1)) (hi (j+1)):ℚ):ℝ) ≤
      etaEulerApprox N (xiGridArgument k:ℝ) := by
    unfold etaEulerApprox
    push_cast
    exact Finset.sum_le_sum (fun j hj => (ht j hj).1)
  have hu : etaEulerApprox N (xiGridArgument k:ℝ) ≤
      ((∑ j ∈ Finset.range N,
        ratEtaRootGridTermUpper N k j B (lo (j+1)) (hi (j+1)):ℚ):ℝ) := by
    unfold etaEulerApprox
    push_cast
    exact Finset.sum_le_sum (fun j hj => (ht j hj).2)
  apply ratRound_interval_enclosure _ _ _ B hB
  · linarith [he.1]
  · push_cast
    push_cast at hu
    linarith [he.2]

theorem ratEtaRootGrid_mem_grid (N k B : ℕ) (lo hi : ℕ → ℚ) (hB : 0 < B) :
    ∃ l u : ℤ, (B:ℚ) * ratEtaRootGridLower N k B lo hi = l ∧
      (B:ℚ) * ratEtaRootGridUpper N k B lo hi = u := by
  obtain ⟨l, _, hl, _⟩ := ratRound_mem_grid
    (∑ j ∈ Finset.range N, ratEtaRootGridTermLower N k j B (lo (j+1)) (hi (j+1))) B hB
  obtain ⟨_, u, _, hu⟩ := ratRound_mem_grid
    ((∑ j ∈ Finset.range N, ratEtaRootGridTermUpper N k j B (lo (j+1)) (hi (j+1))) + 1/2^N) B hB
  exact ⟨l, u, hl, hu⟩

/-- The exact linear weight table can be shared by all nodes. -/
def ratEtaRootTableLower (N k B : ℕ) (lo hi : ℕ → ℚ) : ℚ :=
  ratRoundLower ((ratEtaWeightTable N).mapIdx (fun j w =>
    let c := (-1:ℚ)^j*w
    ratRoundLower (min (c*ratPowRoundLower (lo (j+1)) B (k+40))
      (c*ratPowRoundUpper (hi (j+1)) B (k+40))) B)).sum B

def ratEtaRootTableUpper (N k B : ℕ) (lo hi : ℕ → ℚ) : ℚ :=
  ratRoundUpper (((ratEtaWeightTable N).mapIdx (fun j w =>
    let c := (-1:ℚ)^j*w
    ratRoundUpper (max (c*ratPowRoundLower (lo (j+1)) B (k+40))
      (c*ratPowRoundUpper (hi (j+1)) B (k+40))) B)).sum + 1/2^N) B

theorem ratEtaRootTableLower_eq (N k B : ℕ) (lo hi : ℕ → ℚ) :
    ratEtaRootTableLower N k B lo hi = ratEtaRootGridLower N k B lo hi := by
  unfold ratEtaRootTableLower ratEtaRootGridLower
  rw [ratEtaWeightTable_sum_mapIdx]
  rfl

theorem ratEtaRootTableUpper_eq (N k B : ℕ) (lo hi : ℕ → ℚ) :
    ratEtaRootTableUpper N k B lo hi = ratEtaRootGridUpper N k B lo hi := by
  unfold ratEtaRootTableUpper ratEtaRootGridUpper
  rw [ratEtaWeightTable_sum_mapIdx]
  rfl

end ReciprocalXi


import ProofWorkspace.Final.RationalZetaBoundsFull
import ProofWorkspace.Final.RationalPowerBoundsFull
import ProofWorkspace.Final.RationalPowerDyadicBoundsFull

/-!
# Exact rational eta-integral enclosures

Every alternating Euler summand is enclosed using exact rational real-power
endpoints. The actual analytic remainder is directed and bounded by 2^-N;
it is added only to the upper endpoint.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratEtaCoefficient (N j : ℕ) : ℚ := (-1) ^ j * ratEtaEulerWeight N j

def ratEtaTermLower (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ) : ℚ :=
  min (ratEtaCoefficient N j * ratPowerLower (j + 1) (-s) nLog m nExp)
    (ratEtaCoefficient N j * ratPowerUpper (j + 1) (-s) nLog m nExp)

def ratEtaTermUpper (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ) : ℚ :=
  max (ratEtaCoefficient N j * ratPowerLower (j + 1) (-s) nLog m nExp)
    (ratEtaCoefficient N j * ratPowerUpper (j + 1) (-s) nLog m nExp)

def ratEtaLower (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, ratEtaTermLower N s j nLog m nExp

def ratEtaUpper (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) : ℚ :=
  (∑ j ∈ Finset.range N, ratEtaTermUpper N s j nLog m nExp) + 1 / 2 ^ N

theorem ratEtaCoefficient_cast (N j : ℕ) :
    (ratEtaCoefficient N j : ℝ) = (-1 : ℝ) ^ j * etaEulerWeight N j := by
  unfold ratEtaCoefficient
  push_cast
  rw [ratEtaEulerWeight_cast]

theorem ratEtaTerm_enclosure (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ)
    (hm : 0 < m) (hn : 0 < nExp)
    (hl : |ratPowerLogLower (j + 1) (-s) nLog / m| ≤ 1)
    (hu : |ratPowerLogUpper (j + 1) (-s) nLog / m| ≤ 1) :
    (ratEtaTermLower N s j nLog m nExp : ℝ) ≤
        (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) ∧
      (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) ≤
        (ratEtaTermUpper N s j nLog m nExp : ℝ) := by
  have hp := ratPower_enclosure (j + 1) (-s) nLog m nExp (by positivity) hm hn hl hu
  push_cast at hp
  have he : (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) =
      (ratEtaCoefficient N j : ℝ) * (((j + 1 : ℚ) : ℝ) ^ ((-s : ℚ) : ℝ)) := by
    rw [ratEtaCoefficient_cast]
    push_cast
    rw [Real.rpow_neg (by positivity)]
    rfl
  rw [he]
  unfold ratEtaTermLower ratEtaTermUpper
  push_cast
  rcases le_total (0 : ℝ) (ratEtaCoefficient N j : ℝ) with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp.1 hc),
      (mul_le_mul_of_nonneg_left hp.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hp.2 hc),
      (mul_le_mul_of_nonpos_left hp.1 hc).trans (le_max_left _ _)⟩

/-- All finite terms and the directed analytic tail are enclosed by exact
rational expressions. The range checks contain no unknown real values. -/
theorem ratEtaIntegral_enclosure (N : ℕ) (s : ℚ) (nLog m nExp : ℕ)
    (hs : 0 < s) (hm : 0 < m) (hn : 0 < nExp)
    (hl : ∀ j ∈ Finset.range N, |ratPowerLogLower (j + 1) (-s) nLog / m| ≤ 1)
    (hu : ∀ j ∈ Finset.range N, |ratPowerLogUpper (j + 1) (-s) nLog / m| ≤ 1) :
    (ratEtaLower N s nLog m nExp : ℝ) ≤ etaIntegral (s : ℝ) ∧
      etaIntegral (s : ℝ) ≤ (ratEtaUpper N s nLog m nExp : ℝ) := by
  have he := etaIntegral_euler_error_bounds N (s : ℝ) (by exact_mod_cast hs)
  have hlo : (ratEtaLower N s nLog m nExp : ℝ) ≤ etaEulerApprox N (s : ℝ) := by
    unfold ratEtaLower etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaTerm_enclosure N s j nLog m nExp hm hn (hl j hj) (hu j hj)).1
  have hup : etaEulerApprox N (s : ℝ) ≤
      ((∑ j ∈ Finset.range N, ratEtaTermUpper N s j nLog m nExp : ℚ) : ℝ) := by
    unfold etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaTerm_enclosure N s j nLog m nExp hm hn (hl j hj) (hu j hj)).2
  unfold ratEtaUpper
  push_cast at hup ⊢
  constructor <;> linarith [he.1, he.2]

theorem ratEtaIntegral_width (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) :
    ratEtaUpper N s nLog m nExp - ratEtaLower N s nLog m nExp =
      (∑ j ∈ Finset.range N,
        (ratEtaTermUpper N s j nLog m nExp - ratEtaTermLower N s j nLog m nExp)) +
        1 / 2 ^ N := by
  unfold ratEtaUpper ratEtaLower
  rw [Finset.sum_sub_distrib]
  ring

def ratEtaNatTermLower (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ) : ℚ :=
  min (ratEtaCoefficient N j * ratPowerNatLower (j + 1) (-s) nLog m nExp)
    (ratEtaCoefficient N j * ratPowerNatUpper (j + 1) (-s) nLog m nExp)

def ratEtaNatTermUpper (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ) : ℚ :=
  max (ratEtaCoefficient N j * ratPowerNatLower (j + 1) (-s) nLog m nExp)
    (ratEtaCoefficient N j * ratPowerNatUpper (j + 1) (-s) nLog m nExp)

def ratEtaNatLower (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, ratEtaNatTermLower N s j nLog m nExp

def ratEtaNatUpper (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) : ℚ :=
  (∑ j ∈ Finset.range N, ratEtaNatTermUpper N s j nLog m nExp) + 1 / 2 ^ N

theorem ratEtaNatTerm_enclosure (N : ℕ) (s : ℚ) (j nLog m nExp : ℕ)
    (hm : 0 < m) (hn : 0 < nExp)
    (hl : |ratPowerDyadicLogLower (ratPowerNatMantissa (j + 1)) (-s)
      (Nat.log2 (j + 1)) nLog / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper (ratPowerNatMantissa (j + 1)) (-s)
      (Nat.log2 (j + 1)) nLog / m| ≤ 1) :
    (ratEtaNatTermLower N s j nLog m nExp : ℝ) ≤
        (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) ∧
      (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) ≤
        (ratEtaNatTermUpper N s j nLog m nExp : ℝ) := by
  have hp := ratPowerNat_enclosure (j + 1) (-s) nLog m nExp (by omega) hm hn hl hu
  push_cast at hp
  have he : (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ (s : ℝ) =
      (ratEtaCoefficient N j : ℝ) * (((j : ℝ) + 1) ^ (-(s : ℝ))) := by
    rw [ratEtaCoefficient_cast, Real.rpow_neg (by positivity)]
    rfl
  rw [he]
  unfold ratEtaNatTermLower ratEtaNatTermUpper
  push_cast
  rcases le_total (0 : ℝ) (ratEtaCoefficient N j : ℝ) with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp.1 hc),
      (mul_le_mul_of_nonneg_left hp.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hp.2 hc),
      (mul_le_mul_of_nonpos_left hp.1 hc).trans (le_max_left _ _)⟩

/-- Efficient integer-base eta evaluation: every power uses exact dyadic
range reduction, while the actual analytic error remains one-sided 2^-N. -/
theorem ratEtaNatIntegral_enclosure (N : ℕ) (s : ℚ) (nLog m nExp : ℕ)
    (hs : 0 < s) (hm : 0 < m) (hn : 0 < nExp)
    (hl : ∀ j ∈ Finset.range N,
      |ratPowerDyadicLogLower (ratPowerNatMantissa (j + 1)) (-s)
        (Nat.log2 (j + 1)) nLog / m| ≤ 1)
    (hu : ∀ j ∈ Finset.range N,
      |ratPowerDyadicLogUpper (ratPowerNatMantissa (j + 1)) (-s)
        (Nat.log2 (j + 1)) nLog / m| ≤ 1) :
    (ratEtaNatLower N s nLog m nExp : ℝ) ≤ etaIntegral (s : ℝ) ∧
      etaIntegral (s : ℝ) ≤ (ratEtaNatUpper N s nLog m nExp : ℝ) := by
  have he := etaIntegral_euler_error_bounds N (s : ℝ) (by exact_mod_cast hs)
  have hlo : (ratEtaNatLower N s nLog m nExp : ℝ) ≤ etaEulerApprox N (s : ℝ) := by
    unfold ratEtaNatLower etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaNatTerm_enclosure N s j nLog m nExp hm hn (hl j hj) (hu j hj)).1
  have hup : etaEulerApprox N (s : ℝ) ≤
      ((∑ j ∈ Finset.range N, ratEtaNatTermUpper N s j nLog m nExp : ℚ) : ℝ) := by
    unfold etaEulerApprox
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    exact (ratEtaNatTerm_enclosure N s j nLog m nExp hm hn (hl j hj) (hu j hj)).2
  unfold ratEtaNatUpper
  push_cast at hup ⊢
  constructor <;> linarith [he.1, he.2]

theorem ratEtaNatIntegral_width (N : ℕ) (s : ℚ) (nLog m nExp : ℕ) :
    ratEtaNatUpper N s nLog m nExp - ratEtaNatLower N s nLog m nExp =
      (∑ j ∈ Finset.range N,
        (ratEtaNatTermUpper N s j nLog m nExp - ratEtaNatTermLower N s j nLog m nExp)) +
        1 / 2 ^ N := by
  unfold ratEtaNatUpper ratEtaNatLower
  rw [Finset.sum_sub_distrib]
  ring

end ReciprocalXi

import ProofWorkspace.Final.RationalGammaBoundsFull

noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def ratGammaShiftProduct (q : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (q + j)

theorem gamma_add_nat_product (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : x + n ≠ 0 := ne_of_gt (by positivity)
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hp, ih,
      Finset.prod_range_succ]
    ring

theorem ratGammaShiftProduct_pos (q : ℚ) (hq : 0 < q) (n : ℕ) :
    0 < ratGammaShiftProduct q n := by
  unfold ratGammaShiftProduct
  exact Finset.prod_pos (fun j hj => by positivity)

def gammaGridArgument (k : ℕ) : ℚ := (k + 40) / 160
def gammaGridBase (k : ℕ) : ℚ := 1 / 2 + (((k - 40) % 160 : ℕ) : ℚ) / 160
def gammaGridOffset (k : ℕ) : ℚ :=
  if k < 40 then gammaGridArgument k else gammaGridBase k - 1
def gammaGridMultiplier (k : ℕ) : ℚ :=
  if k < 40 then (gammaGridArgument k)⁻¹
  else ratGammaShiftProduct (gammaGridBase k) ((k - 40) / 160)

theorem gammaGridArgument_pos (k : ℕ) : 0 < gammaGridArgument k := by
  unfold gammaGridArgument
  positivity

theorem gammaGridBase_bounds (k : ℕ) :
    1 / 2 ≤ gammaGridBase k ∧ gammaGridBase k < 3 / 2 := by
  have hm : (k - 40) % 160 < 160 := Nat.mod_lt _ (by norm_num)
  have hmR : (((k - 40) % 160 : ℕ) : ℚ) < 160 := by exact_mod_cast hm
  have hm0 : (0 : ℚ) ≤ ((k - 40) % 160 : ℕ) := by positivity
  unfold gammaGridBase
  constructor <;> linarith

theorem gammaGridOffset_bounds (k : ℕ) : |gammaGridOffset k| ≤ 1 / 2 := by
  unfold gammaGridOffset
  split_ifs with hk
  · have hkr : (k : ℚ) < 40 := by exact_mod_cast hk
    rw [abs_of_pos (gammaGridArgument_pos k)]
    unfold gammaGridArgument
    linarith
  · rw [abs_le]
    have hb := gammaGridBase_bounds k
    constructor <;> linarith

theorem gammaGridArgument_eq_base_shift (k : ℕ) (hk : 40 ≤ k) :
    gammaGridArgument k = gammaGridBase k + ((k - 40) / 160 : ℕ) := by
  have hd := Nat.mod_add_div (k - 40) 160
  have he : (k - 40) % 160 + 160 * ((k - 40) / 160) + 40 = k := by omega
  have heq : (((k - 40) % 160 : ℕ) : ℚ) +
      160 * (((k - 40) / 160 : ℕ) : ℚ) + 40 = (k : ℚ) := by exact_mod_cast he
  unfold gammaGridArgument gammaGridBase
  linarith

theorem gammaGridMultiplier_pos (k : ℕ) : 0 < gammaGridMultiplier k := by
  unfold gammaGridMultiplier
  split_ifs
  · exact inv_pos.mpr (gammaGridArgument_pos k)
  · exact ratGammaShiftProduct_pos _ (lt_of_lt_of_le (by norm_num)
      (gammaGridBase_bounds k).1) _

/-- Exact positive Gamma recurrence reducing every retained-grid argument
to the already certified interval [1/2,3/2]. -/
theorem gammaGrid_recurrence (k : ℕ) :
    Real.Gamma (gammaGridArgument k : ℝ) = (gammaGridMultiplier k : ℝ) *
      Real.Gamma (1 + (gammaGridOffset k : ℝ)) := by
  unfold gammaGridMultiplier gammaGridOffset
  split_ifs with hk
  · have hp : 0 < (gammaGridArgument k : ℝ) := by
      exact_mod_cast gammaGridArgument_pos k
    rw [add_comm (1 : ℝ), Real.Gamma_add_one (ne_of_gt hp)]
    push_cast
    field_simp
  · have hr := gammaGridArgument_eq_base_shift k (by omega)
    have hb : 0 < (gammaGridBase k : ℝ) := by
      have h := (gammaGridBase_bounds k).1
      have hr : (1 / 2 : ℝ) ≤ (gammaGridBase k : ℝ) := by
        have hr' : ((1 / 2 : ℚ) : ℝ) ≤ (gammaGridBase k : ℝ) := Rat.cast_le.mpr h
        norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hr'
        exact hr'
      linarith
    rw [hr]
    push_cast
    have ho : 1 + ((gammaGridBase k : ℝ) - 1) = (gammaGridBase k : ℝ) := by ring
    rw [ho, gamma_add_nat_product _ hb]
    unfold ratGammaShiftProduct
    push_cast
    ring

def ratGammaGridLower (k N M L m n : ℕ) : ℚ :=
  gammaGridMultiplier k * ratGammaLower (gammaGridOffset k) N M L m n
def ratGammaGridUpper (k N M L m n : ℕ) : ℚ :=
  gammaGridMultiplier k * ratGammaUpper (gammaGridOffset k) N M L m n

theorem ratGammaGrid_enclosure (k N M L m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hl : |ratLogGammaLower (gammaGridOffset k) N M L / m| ≤ 1)
    (hu : |ratLogGammaUpper (gammaGridOffset k) N M L / m| ≤ 1) :
    (ratGammaGridLower k N M L m n : ℝ) ≤ Real.Gamma (gammaGridArgument k : ℝ) ∧
    Real.Gamma (gammaGridArgument k : ℝ) ≤ (ratGammaGridUpper k N M L m n : ℝ) := by
  have h := ratGamma_enclosure (gammaGridOffset k) N M L m n
    (gammaGridOffset_bounds k) hm hn hl hu
  have hp : 0 ≤ (gammaGridMultiplier k : ℝ) := by
    exact_mod_cast (gammaGridMultiplier_pos k).le
  unfold ratGammaGridLower ratGammaGridUpper
  push_cast
  rw [gammaGrid_recurrence]
  exact ⟨mul_le_mul_of_nonneg_left h.1 hp, mul_le_mul_of_nonneg_left h.2 hp⟩

end ReciprocalXi


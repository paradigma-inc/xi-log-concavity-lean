import ProofWorkspace.Final.RootEtaIntegerArithmeticFull

set_option autoImplicit false
namespace ReciprocalXi

structure RoundedRootState where
  lowerRoot : ℤ
  upperRoot : ℤ
  lowerPower : ℤ
  upperPower : ℤ
deriving DecidableEq, Repr

def roundedRootSeed (l u : ℤ) (B n : ℕ) : RoundedRootState :=
  ⟨l, u, intPowRoundLower l B n, intPowRoundUpper u B n⟩

def roundedRootStep (B : ℕ) (s : RoundedRootState) : RoundedRootState :=
  ⟨s.lowerRoot, s.upperRoot,
    s.lowerPower*s.lowerRoot/(B:ℤ), -(-(s.upperPower*s.upperRoot)/(B:ℤ))⟩

theorem roundedRootStep_seed (l u : ℤ) (B n : ℕ) :
    roundedRootStep B (roundedRootSeed l u B n) = roundedRootSeed l u B (n+1) := rfl

theorem roundedRootStep_iterate_seed (l u : ℤ) (B n k : ℕ) :
    (roundedRootStep B)^[k] (roundedRootSeed l u B n) = roundedRootSeed l u B (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, roundedRootStep_seed]
    rfl

def roundedRootTableAt (rows : List RootCertificateRow) (B n : ℕ) : List RoundedRootState :=
  rows.map (fun r => roundedRootSeed r.l r.u B n)

def roundedRootTableAdvance (B k : ℕ) (s : List RoundedRootState) : List RoundedRootState :=
  (List.map (roundedRootStep B))^[k] s

theorem roundedRootTable_next (rows : List RootCertificateRow) (B n : ℕ) :
    (roundedRootTableAt rows B n).map (roundedRootStep B) = roundedRootTableAt rows B (n+1) := by
  simp only [roundedRootTableAt, List.map_map]
  congr 1

theorem roundedRootTableAdvance_eq (rows : List RootCertificateRow) (B n k : ℕ) :
    roundedRootTableAdvance B k (roundedRootTableAt rows B n) = roundedRootTableAt rows B (n+k) := by
  induction k with
  | zero => simp [roundedRootTableAdvance]
  | succ k ih =>
    unfold roundedRootTableAdvance at ih ⊢
    rw [Function.iterate_succ_apply', ih, roundedRootTable_next]
    rfl

theorem roundedRootTableAt_length (rows : List RootCertificateRow) (B n : ℕ) :
    (roundedRootTableAt rows B n).length = rows.length := by simp [roundedRootTableAt]

theorem roundedRootTableAdvance_length (B k : ℕ) (s : List RoundedRootState) :
    (roundedRootTableAdvance B k s).length = s.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold roundedRootTableAdvance at ih ⊢
    rw [Function.iterate_succ_apply', List.length_map, ih]

theorem roundedRootState_actual_enclosure (a : ℚ) (l u : ℤ) (B k : ℕ)
    (ha : 0 < a) (hB : 0 < B)
    (hl : 0 ≤ (l:ℚ)/B) (hu : 0 ≤ (u:ℚ)/B)
    (hlo : a*((l:ℚ)/B)^80 ≤ 1) (hup : 1 ≤ a*((u:ℚ)/B)^80) :
    let s := (roundedRootStep B)^[k] (roundedRootSeed l u B 40)
    (((s.lowerPower:ℚ)/B:ℚ):ℝ) ≤ (a:ℝ)^(-(xiGridArgument k:ℝ)) ∧
      (a:ℝ)^(-(xiGridArgument k:ℝ)) ≤ (((s.upperPower:ℚ)/B:ℚ):ℝ) := by
  dsimp only
  rw [roundedRootStep_iterate_seed]
  simp only [roundedRootSeed, Nat.add_comm 40 k]
  rw [intPowRoundLower_eq _ _ _ hB, intPowRoundUpper_eq _ _ _ hB]
  exact ratRoot80Grid_enclosure a ((l:ℚ)/B) ((u:ℚ)/B) k B ha hB hl hu hlo hup

def rootStateFor (a k : ℕ) : RoundedRootState :=
  let r := rootCertificateRows.get (rootCertificateIndex a)
  roundedRootSeed r.l r.u rootCertificateScale (k+40)

theorem rootStateFor_next (a k : ℕ) :
    roundedRootStep rootCertificateScale (rootStateFor a k) = rootStateFor a (k+1) := by
  unfold rootStateFor
  rw [roundedRootStep_seed]

def weightedRootStateLowerTerm (c : ℚ) (s : RoundedRootState) : ℤ :=
  min (c.num*s.lowerPower) (c.num*s.upperPower) / (c.den:ℤ)
def weightedRootStateUpperTerm (c : ℚ) (s : RoundedRootState) : ℤ :=
  -(-max (c.num*s.lowerPower) (c.num*s.upperPower) / (c.den:ℤ))

theorem weightedRootStateLowerTerm_eq (w : ℚ) (j k : ℕ) :
    weightedRootStateLowerTerm ((-1:ℚ)^j*w) (rootStateFor (j+1) k) =
      intEtaRootLowerTerm w j k := rfl

theorem weightedRootStateUpperTerm_eq (w : ℚ) (j k : ℕ) :
    weightedRootStateUpperTerm ((-1:ℚ)^j*w) (rootStateFor (j+1) k) =
      intEtaRootUpperTerm w j k := rfl

end ReciprocalXi


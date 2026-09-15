import ProofWorkspace.Final.FastGammaBoundsFull
import ProofWorkspace.Final.IntegerEtaArithmeticFull
import ProofWorkspace.Final.RoundedSeriesScansFull

set_option autoImplicit false

namespace ReciprocalXi

def ratZetaPairFromWeights (ws : List ℚ) (M k B : ℕ) : ℚ × ℚ :=
  let lo : ℚ := ((ws.mapIdx (fun j w => intEtaTermLower w j k B)).sum : ℤ) / B
  let hi : ℚ := ((ws.mapIdx (fun j w => intEtaTermUpper w j k B)).sum : ℤ) / B
  (ratRoundLower (ratZetaNatFactor k * lo) B,
    ratRoundUpper (ratZetaNatFactor k * hi + 2/(2:ℚ)^M) B)

theorem ratZetaPairFromWeights_eq (M k B : ℕ) :
    ratZetaPairFromWeights (ratEtaWeightTable M) M k B =
      (ratZetaNatRoundedLower M k B, ratZetaNatRoundedUpper M k B) := by
  change (ratRoundLower (ratZetaNatFactor k * ratEtaIntegerFastLower M k B) B,
    ratRoundUpper (ratZetaNatFactor k * ratEtaIntegerFastUpper M k B + 2/(2:ℚ)^M) B) = _
  rw [ratEtaIntegerFastLower_eq, ratEtaIntegerFastUpper_eq]
  rfl

/-- One Euler-weight table supplies all integer-zeta coefficients. -/
def ratGammaZetaTable (N M B : ℕ) : List (ℚ × ℚ) :=
  let ws := ratEtaWeightTable M
  (List.range N).map (fun k => ratZetaPairFromWeights ws M (k+2) B)

theorem ratGammaZetaTable_eq (N M B : ℕ) :
    ratGammaZetaTable N M B = (List.range N).map (fun k =>
      (ratZetaNatRoundedLower M (k+2) B, ratZetaNatRoundedUpper M (k+2) B)) := by
  simp only [ratGammaZetaTable, ratZetaPairFromWeights_eq]

def ratGammaSeriesFromTable (z : ℚ) (zs : List (ℚ × ℚ)) (B : ℕ) : ℚ × ℚ :=
  let terms := zs.mapIdx (fun k p =>
    let c := ratGammaLogCoefficient z k
    (ratRoundLower (min (c*p.1) (c*p.2)) B,
      ratRoundUpper (max (c*p.1) (c*p.2)) B))
  ((terms.map Prod.fst).sum, (terms.map Prod.snd).sum)

theorem ratGammaSeriesFromTable_eq (z : ℚ) (N M B : ℕ) :
    ratGammaSeriesFromTable z (ratGammaZetaTable N M B) B =
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B,
        ∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B) := by
  have ht : ((ratGammaZetaTable N M B).mapIdx (fun k p =>
      let c := ratGammaLogCoefficient z k
      (ratRoundLower (min (c*p.1) (c*p.2)) B,
        ratRoundUpper (max (c*p.1) (c*p.2)) B))) =
      (List.range N).map (fun k =>
        (ratGammaCoefficientRoundedLower z k M B, ratGammaCoefficientRoundedUpper z k M B)) := by
    apply List.ext_getElem
    · simp [ratGammaZetaTable_eq]
    · intro k hk hk'; simp [ratGammaZetaTable_eq, ratGammaCoefficientRoundedLower,
        ratGammaCoefficientRoundedUpper]
  unfold ratGammaSeriesFromTable
  rw [ht]
  have hs (f : ℕ → ℚ) (n : ℕ) : ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  simp only [List.map_map, Function.comp_def, hs]

def ratLogGammaTablePair (z : ℚ) (N M L B : ℕ) : ℚ × ℚ :=
  let s := ratGammaSeriesFromTable z (ratGammaZetaTable N M B) B
  (ratRoundLower (ratGammaConstantFastLower z L B + s.1 - 8*(1/2:ℚ)^(N+2)) B,
    ratRoundUpper (ratGammaConstantFastUpper z L B + s.2 + 8*(1/2:ℚ)^(N+2)) B)

theorem ratLogGammaTablePair_eq (z : ℚ) (N M L B : ℕ) :
    ratLogGammaTablePair z N M L B =
      (ratLogGammaFastLower z N M L B, ratLogGammaFastUpper z N M L B) := by
  unfold ratLogGammaTablePair
  rw [ratGammaSeriesFromTable_eq]
  rfl

end ReciprocalXi


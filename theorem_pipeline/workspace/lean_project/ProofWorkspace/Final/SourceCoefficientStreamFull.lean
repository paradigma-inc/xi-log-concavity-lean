import ProofWorkspace.Final.SourceCoefficientErrorFull
import ProofWorkspace.Final.IntegerPowerArithmeticFull

set_option autoImplicit false
namespace ReciprocalXi

def sourceGridDecode (a : ℤ) : ℚ := (a:ℚ)/sourceCoefficientScale
def sourceGridDecodePair (a : ℤ × ℤ) : ℚ × ℚ :=
  (sourceGridDecode a.1, sourceGridDecode a.2)

private theorem coefficientScale_pos : 0 < sourceCoefficientScale := by
  norm_num [sourceCoefficientScale]

private theorem coefficientScale_ne : (sourceCoefficientScale:ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt coefficientScale_pos

def intSourceWeightStart (p : ℚ) (v : ℕ → ℚ) (k : ℕ) : ℤ :=
  Int.floor ((sourceCoefficientScale:ℚ) * ((1/(40*p))*v k*(if k=0 then 1/2 else 1)))

def intSourceWeightStep (w : ℤ) (j k : ℕ) : ℤ :=
  w*(k:ℤ)/(8000*(j+1:ℕ))

theorem intSourceWeightStart_eq (p : ℚ) (v : ℕ → ℚ) (k : ℕ) :
    sourceGridDecode (intSourceWeightStart p v k) =
      ratSourceRoundedWeight p v sourceCoefficientScale 0 k := rfl

theorem intSourceWeightStep_eq (w : ℤ) (j k : ℕ) :
    sourceGridDecode (intSourceWeightStep w j k) =
      ratRoundLower (sourceGridDecode w * sourceWeightMultiplier j k) sourceCoefficientScale := by
  have he : (sourceCoefficientScale:ℚ)*(sourceGridDecode w * sourceWeightMultiplier j k) =
      ((w*(k:ℤ):ℤ):ℚ)/((8000*(j+1):ℕ):ℚ) := by
    unfold sourceGridDecode sourceWeightMultiplier
    push_cast
    calc
      _ = ((w:ℚ)*(k:ℚ)/(8000*((j:ℚ)+1))) *
          ((sourceCoefficientScale:ℚ)/(sourceCoefficientScale:ℚ)) := by ring
      _ = _ := by rw [div_self coefficientScale_ne, mul_one]
  unfold ratRoundLower
  rw [he, Int.floor_div_natCast, Int.floor_intCast]
  rfl

def intSourceTrigSeed (q : ℚ) : ℤ × ℤ :=
  (Int.floor ((sourceCoefficientScale:ℚ)*ratSourceCosTaylor q),
    Int.floor ((sourceCoefficientScale:ℚ)*ratSourceSinTaylor q))

def intSourceTrigStep (r t : ℤ × ℤ) : ℤ × ℤ :=
  ((t.1*r.1-t.2*r.2)/(sourceCoefficientScale:ℤ),
    (t.2*r.1+t.1*r.2)/(sourceCoefficientScale:ℤ))

theorem intSourceTrigSeed_eq (q : ℚ) :
    sourceGridDecodePair (intSourceTrigSeed q) = ratSourceRoundedTrigSeed q := rfl

theorem intSourceTrigStep_eq (r t : ℤ × ℤ) :
    sourceGridDecodePair (intSourceTrigStep r t) =
      (ratRoundLower (sourceGridDecode t.1*sourceGridDecode r.1-
        sourceGridDecode t.2*sourceGridDecode r.2) sourceCoefficientScale,
       ratRoundLower (sourceGridDecode t.2*sourceGridDecode r.1+
        sourceGridDecode t.1*sourceGridDecode r.2) sourceCoefficientScale) := by
  have hsub : (sourceCoefficientScale:ℚ)*
      (sourceGridDecode t.1*sourceGridDecode r.1-sourceGridDecode t.2*sourceGridDecode r.2) =
        ((t.1*r.1-t.2*r.2:ℤ):ℚ)/sourceCoefficientScale := by
    unfold sourceGridDecode
    push_cast
    field_simp [coefficientScale_ne]
  have hadd : (sourceCoefficientScale:ℚ)*
      (sourceGridDecode t.2*sourceGridDecode r.1+sourceGridDecode t.1*sourceGridDecode r.2) =
        ((t.2*r.1+t.1*r.2:ℤ):ℚ)/sourceCoefficientScale := by
    unfold sourceGridDecode
    push_cast
    field_simp [coefficientScale_ne]
  unfold ratRoundLower
  rw [hsub, hadd, Int.floor_div_natCast, Int.floor_div_natCast,
    Int.floor_intCast, Int.floor_intCast]
  rfl

theorem intSourceTrigStep_matches (q : ℚ) (k : ℕ) (t : ℤ × ℤ)
    (ht : sourceGridDecodePair t = ratSourceRoundedTrig q k) :
    sourceGridDecodePair (intSourceTrigStep (intSourceTrigSeed q) t) =
      ratSourceRoundedTrig q (k+1) := by
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  have hr1 := congrArg Prod.fst (intSourceTrigSeed_eq q)
  have hr2 := congrArg Prod.snd (intSourceTrigSeed_eq q)
  dsimp only [sourceGridDecodePair] at ht1 ht2 hr1 hr2
  rw [intSourceTrigStep_eq, ht1, ht2, hr1, hr2]
  rfl

def intSourceTrigFactor (j : ℕ) (t : ℤ × ℤ) : ℤ :=
  (if j%4=1 ∨ j%4=2 then -1 else 1) * (if j%2=0 then t.1 else t.2)

theorem intSourceTrigFactor_eq (q : ℚ) (j k : ℕ) (t : ℤ × ℤ)
    (ht : sourceGridDecodePair t = ratSourceRoundedTrig q k) :
    sourceGridDecode (intSourceTrigFactor j t) = ratSourceRoundedTrigFactor q j k := by
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  dsimp only [sourceGridDecodePair] at ht1 ht2
  by_cases hj4 : j%4=1 ∨ j%4=2 <;> by_cases hj2 : j%2=0 <;>
    simp [intSourceTrigFactor, ratSourceRoundedTrigFactor, hj4, hj2,
      sourceGridDecode, ←ht1, ←ht2, neg_div]

def intSourceCoefficientTerm (w : ℤ) (j : ℕ) (t : ℤ × ℤ) : ℤ :=
  w * intSourceTrigFactor j t / (sourceCoefficientScale:ℤ)

theorem intSourceCoefficientTerm_eq (w : ℤ) (j : ℕ) (t : ℤ × ℤ) :
    sourceGridDecode (intSourceCoefficientTerm w j t) =
      ratRoundLower (sourceGridDecode w * sourceGridDecode (intSourceTrigFactor j t))
        sourceCoefficientScale := by
  exact (ratRoundLower_scaled_product w (intSourceTrigFactor j t)
    sourceCoefficientScale coefficientScale_pos).symm

def intSourceCoefficientTermsFrom (t : ℤ × ℤ) (k : ℕ) : ℕ → ℕ → ℤ → List ℤ
  | _, 0, _ => []
  | j, n+1, w => intSourceCoefficientTerm w j t ::
      intSourceCoefficientTermsFrom t k (j+1) n (intSourceWeightStep w j k)

theorem intSourceCoefficientTermsFrom_eq (p : ℚ) (v : ℕ → ℚ) (q : ℚ)
    (k : ℕ) (t : ℤ × ℤ) (ht : sourceGridDecodePair t = ratSourceRoundedTrig q k)
    (j n : ℕ) (w : ℤ)
    (hw : sourceGridDecode w = ratSourceRoundedWeight p v sourceCoefficientScale j k) :
    (intSourceCoefficientTermsFrom t k j n w).map sourceGridDecode =
      (List.range' j n).map (fun i => ratRoundLower
        (ratSourceRoundedWeight p v sourceCoefficientScale i k * ratSourceRoundedTrigFactor q i k)
        sourceCoefficientScale) := by
  induction n generalizing j w with
  | zero => rfl
  | succ n ih =>
    simp only [intSourceCoefficientTermsFrom, List.map_cons, List.range'_succ]
    apply congrArg₂ List.cons
    · rw [intSourceCoefficientTerm_eq, hw, intSourceTrigFactor_eq q j k t ht]
    · apply ih
      rw [intSourceWeightStep_eq, hw]
      rfl

def ratSourceCoefficientSummand (q p : ℚ) (v : ℕ → ℚ) (j k : ℕ) : ℚ :=
  ratRoundLower (ratSourceRoundedWeight p v sourceCoefficientScale j k *
    ratSourceRoundedTrigFactor q j k) sourceCoefficientScale

def intSourceCoefficientStreamFrom (p : ℚ) (v : ℕ → ℚ) (r : ℤ × ℤ)
    (degreeCount : ℕ) : ℕ → ℕ → ℤ × ℤ → List ℤ → List ℤ
  | _, 0, _, acc => acc
  | k, count+1, t, acc =>
    intSourceCoefficientStreamFrom p v r degreeCount (k+1) count (intSourceTrigStep r t)
      (List.zipWith (·+·) acc
        (intSourceCoefficientTermsFrom t k 0 degreeCount (intSourceWeightStart p v k)))

private theorem sourceGridDecode_zip_add (a b : List ℤ) :
    (List.zipWith (·+·) a b).map sourceGridDecode =
      List.zipWith (·+·) (a.map sourceGridDecode) (b.map sourceGridDecode) := by
  induction a generalizing b with
  | nil => simp
  | cons a as ih =>
    cases b with
    | nil => simp
    | cons b bs => simp [sourceGridDecode, Int.cast_add, add_div, ih]

private theorem source_zip_add_map (xs : List ℕ) (a b : ℕ → ℚ) :
    List.zipWith (·+·) (xs.map a) (xs.map b) = xs.map (fun j => a j+b j) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem intSourceCoefficientStreamFrom_eq (q p : ℚ) (v : ℕ → ℚ)
    (degreeCount k count : ℕ) (t : ℤ × ℤ) (acc : List ℤ) (a : ℕ → ℚ)
    (ht : sourceGridDecodePair t = ratSourceRoundedTrig q k)
    (ha : acc.map sourceGridDecode = (List.range degreeCount).map a) :
    (intSourceCoefficientStreamFrom p v (intSourceTrigSeed q) degreeCount k count t acc).map
        sourceGridDecode =
      (List.range degreeCount).map (fun j => a j+
        ((List.range' k count).map (ratSourceCoefficientSummand q p v j)).sum) := by
  induction count generalizing k t acc a with
  | zero => simpa only [intSourceCoefficientStreamFrom, List.range'_zero, List.map_nil,
      List.sum_nil, add_zero] using ha
  | succ count ih =>
    have hrow : (intSourceCoefficientTermsFrom t k 0 degreeCount (intSourceWeightStart p v k)).map
        sourceGridDecode =
        (List.range degreeCount).map (fun j => ratSourceCoefficientSummand q p v j k) := by
      simpa only [←List.range_eq_range', ratSourceCoefficientSummand] using
        intSourceCoefficientTermsFrom_eq p v q k t ht 0 degreeCount
          (intSourceWeightStart p v k) (intSourceWeightStart_eq p v k)
    have hacc : (List.zipWith (·+·) acc
        (intSourceCoefficientTermsFrom t k 0 degreeCount (intSourceWeightStart p v k))).map
          sourceGridDecode =
        (List.range degreeCount).map (fun j => a j+ratSourceCoefficientSummand q p v j k) := by
      rw [sourceGridDecode_zip_add, ha, hrow, source_zip_add_map]
    have h := ih (k+1) (intSourceTrigStep (intSourceTrigSeed q) t)
      (List.zipWith (·+·) acc
        (intSourceCoefficientTermsFrom t k 0 degreeCount (intSourceWeightStart p v k)))
      (fun j => a j+ratSourceCoefficientSummand q p v j k)
      (intSourceTrigStep_matches q k t ht) hacc
    simpa only [intSourceCoefficientStreamFrom, List.range'_succ, List.map_cons,
      List.sum_cons, add_assoc] using h

def intSourceCoefficientStream (c p : ℚ) (v : ℕ → ℚ) : List ℤ :=
  intSourceCoefficientStreamFrom p v (intSourceTrigSeed (c/40)) 65 0 13601
    ((sourceCoefficientScale:ℤ),0) (List.replicate 65 0)

private theorem sourceGridDecode_replicate (n : ℕ) :
    (List.replicate n (0:ℤ)).map sourceGridDecode = (List.range n).map (fun _ => (0:ℚ)) := by
  simp [sourceGridDecode]

private theorem source_sum_list_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem intSourceCoefficientStream_eq (c p : ℚ) (v : ℕ → ℚ) :
    (intSourceCoefficientStream c p v).map sourceGridDecode =
      (List.range 65).map (ratSourceRoundedCoefficient c p v) := by
  have ht : sourceGridDecodePair ((sourceCoefficientScale:ℤ),0) = ratSourceRoundedTrig (c/40) 0 := by
    simp [sourceGridDecodePair, sourceGridDecode, ratSourceRoundedTrig,
      ne_of_gt coefficientScale_pos]
  have h := intSourceCoefficientStreamFrom_eq (c/40) p v 65 0 13601
    ((sourceCoefficientScale:ℤ),0) (List.replicate 65 0) (fun _ => 0) ht
    (sourceGridDecode_replicate 65)
  simpa only [intSourceCoefficientStream, zero_add, ←List.range_eq_range', source_sum_list_range,
    ratSourceCoefficientSummand, ratSourceRoundedCoefficient] using h

theorem intSourceCoefficientStream_length (c p : ℚ) (v : ℕ → ℚ) :
    (intSourceCoefficientStream c p v).length = 65 := by
  have h := congrArg List.length (intSourceCoefficientStream_eq c p v)
  simpa only [List.length_map, List.length_range] using h

def ratSourceStreamCoefficient (c p : ℚ) (v : ℕ → ℚ) (j : Fin 65) : ℚ :=
  sourceGridDecode ((intSourceCoefficientStream c p v)[j.val]'(by
    rw [intSourceCoefficientStream_length]
    exact j.isLt))

theorem ratSourceStreamCoefficient_eq (c p : ℚ) (v : ℕ → ℚ) (j : Fin 65) :
    ratSourceStreamCoefficient c p v j = ratSourceRoundedCoefficient c p v j.val := by
  have h := congrArg (fun l : List ℚ => l[j.val]?) (intSourceCoefficientStream_eq c p v)
  dsimp only at h
  have hj : j.val < (intSourceCoefficientStream c p v).length := by
    rw [intSourceCoefficientStream_length]
    exact j.isLt
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_range j.isLt] at h
  exact Option.some.inj h

theorem ratSourceStreamCoefficient_error_budget (c p : ℚ) (v : ℕ → ℚ) (j : Fin 65)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 40) (hp : 3 ≤ p)
    (hv : ∀ k, k ≤ 13600 → |(v k:ℝ)| ≤ 43046722) :
    |(ratSourceStreamCoefficient c p v j:ℝ)-
      (realSampledTaylorPolynomial (c:ℝ) (p:ℝ) (fun k => (v k:ℝ))).coeff j.val| ≤
        (13601:ℝ)*sourceRoundedCoefficientTermBudget := by
  rw [ratSourceStreamCoefficient_eq]
  exact ratSourceRoundedCoefficient_error_budget c p v j.val hc0 hc1 hp (by omega) hv

theorem ratSourceStreamCoefficient_error_lt (c p : ℚ) (v : ℕ → ℚ) (j : Fin 65)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 40) (hp : 3 ≤ p)
    (hv : ∀ k, k ≤ 13600 → |(v k:ℝ)| ≤ 43046722) :
    |(ratSourceStreamCoefficient c p v j:ℝ)-
      (realSampledTaylorPolynomial (c:ℝ) (p:ℝ) (fun k => (v k:ℝ))).coeff j.val| <
        1/(10:ℝ)^140 :=
  (ratSourceStreamCoefficient_error_budget c p v j hc0 hc1 hp hv).trans_lt
    sourceRoundedCoefficientBudget_lt

end ReciprocalXi


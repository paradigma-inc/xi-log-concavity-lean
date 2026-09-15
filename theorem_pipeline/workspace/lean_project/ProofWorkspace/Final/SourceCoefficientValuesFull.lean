import ProofWorkspace.Final.SourceCoefficientStreamFull

set_option autoImplicit false
namespace ReciprocalXi

/-- Consume samples directly, avoiding kernel-linear indexed lookup at each step. -/
def intSourceCoefficientValuesFrom (p : ℚ) (r : ℤ × ℤ) (degreeCount : ℕ) :
    ℕ → List ℚ → ℤ × ℤ → List ℤ → List ℤ
  | _, [], _, acc => acc
  | k, v::vs, t, acc =>
    intSourceCoefficientValuesFrom p r degreeCount (k+1) vs (intSourceTrigStep r t)
      (List.zipWith (·+·) acc
        (intSourceCoefficientTermsFrom t k 0 degreeCount
          (intSourceWeightStart p (fun _ => v) k)))

theorem intSourceCoefficientValuesFrom_map (p : ℚ) (r : ℤ × ℤ)
    (degreeCount k count : ℕ) (v : ℕ → ℚ) (t : ℤ × ℤ) (acc : List ℤ) :
    intSourceCoefficientValuesFrom p r degreeCount k ((List.range' k count).map v) t acc =
      intSourceCoefficientStreamFrom p v r degreeCount k count t acc := by
  induction count generalizing k t acc with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, intSourceCoefficientValuesFrom,
      intSourceCoefficientStreamFrom]
    exact ih (k+1) (intSourceTrigStep r t) _

def intSourceCoefficientValues (c p : ℚ) (xs : List ℚ) : List ℤ :=
  intSourceCoefficientValuesFrom p (intSourceTrigSeed (c/40)) 65 0 xs
    ((sourceCoefficientScale:ℤ),0) (List.replicate 65 0)

theorem intSourceCoefficientValues_eq_stream (c p : ℚ) (v : ℕ → ℚ) (xs : List ℚ)
    (hxs : xs = (List.range 13601).map v) :
    intSourceCoefficientValues c p xs = intSourceCoefficientStream c p v := by
  unfold intSourceCoefficientValues intSourceCoefficientStream
  rw [hxs, List.range_eq_range']
  exact intSourceCoefficientValuesFrom_map p (intSourceTrigSeed (c/40)) 65 0 13601 v _ _

theorem sourceArray_toList_eq_samples (xs : Array ℚ) (n : ℕ) (hn : xs.size = n) :
    xs.toList = (List.range n).map (fun k => xs.getD k 0) := by
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_range] using hn
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hk : i < xs.size := hi
    rw [Array.getD, dif_pos hk]
    rfl

theorem intSourceCoefficientValues_array_eq_stream (c p : ℚ) (xs : Array ℚ)
    (hx : xs.size = 13601) :
    intSourceCoefficientValues c p xs.toList =
      intSourceCoefficientStream c p (fun k => xs.getD k 0) :=
  intSourceCoefficientValues_eq_stream c p (fun k => xs.getD k 0) xs.toList
    (sourceArray_toList_eq_samples xs 13601 hx)

end ReciprocalXi

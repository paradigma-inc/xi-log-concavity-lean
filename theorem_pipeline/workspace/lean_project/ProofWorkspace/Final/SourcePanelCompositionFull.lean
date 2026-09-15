import ProofWorkspace.Final.SourceCoefficientValuesFull
import ProofWorkspace.Final.SourcePanel317CheckpointsFull
import ProofWorkspace.Final.SourcePanel317BoundsFull

set_option autoImplicit false
namespace ReciprocalXi

/-- Splitting the finite source calculation preserves both the rotation state and accumulator. -/
theorem intSourceCoefficientValuesFrom_append (p : ℚ) (r : ℤ × ℤ)
    (d k : ℕ) (xs ys : List ℚ) (t : ℤ × ℤ) (acc : List ℤ) :
    intSourceCoefficientValuesFrom p r d k (xs++ys) t acc =
      intSourceCoefficientValuesFrom p r d (k+xs.length) ys
        ((intSourceTrigStep r)^[xs.length] t)
        (intSourceCoefficientValuesFrom p r d k xs t acc) := by
  induction xs generalizing k t acc with
  | nil => simp [intSourceCoefficientValuesFrom]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, intSourceCoefficientValuesFrom,
      Function.iterate_succ_apply]
    rw [ih]
    congr 1; omega


def sourcePanel317Remaining (i : ℕ) : List ℤ :=
  intSourceCoefficientValuesFrom sourcePiMidpoint sourcePanel317Seed 65
    (min (256*i) 13601) (sourceMidpointArray.toList.drop (min (256*i) 13601))
    (sourcePanel317Checkpoint i).1 (sourcePanel317Checkpoint i).2

theorem sourcePanel317Remaining_step (i : ℕ) (hi : i < 54)
    (hc : sourcePanel317ChunkCheck i) :
    sourcePanel317Remaining i = sourcePanel317Remaining (i+1) := by
  have hk : min (256*i) 13601 = 256*i := Nat.min_eq_left (by omega)
  have hs : 256*i + min 256 (13601-256*i) = min (256*(i+1)) 13601 := by omega
  have harray : sourceMidpointArray.toList.length = 13601 := sourceMidpointArray_size
  have hlen : ((sourceMidpointArray.toList.drop (256*i)).take
      (min 256 (13601-256*i))).length = min 256 (13601-256*i) := by
    rw [List.length_take, List.length_drop, harray]
    exact Nat.min_eq_left (by omega)
  have hdrop : (sourceMidpointArray.toList.drop (256*i)).drop
      (min 256 (13601-256*i)) =
        sourceMidpointArray.toList.drop (min (256*(i+1)) 13601) := by
    rw [List.drop_drop]
    congr 1
  unfold sourcePanel317ChunkCheck at hc
  have ht := congrArg Prod.fst hc
  have ha := congrArg Prod.snd hc
  dsimp only at ht ha
  unfold sourcePanel317Remaining
  rw [hk, ←List.take_append_drop (min 256 (13601-256*i))
    (sourceMidpointArray.toList.drop (256*i))]
  rw [intSourceCoefficientValuesFrom_append, hlen, hdrop, hs]
  rw [ht, ha]

theorem sourcePanel317Remaining_all
    (hc : ∀ i : Fin 54, sourcePanel317ChunkCheck i) (i : ℕ) (hi : i ≤ 54) :
    sourcePanel317Remaining 0 = sourcePanel317Remaining i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (ih (by omega)).trans
      (sourcePanel317Remaining_step i (by omega) (hc ⟨i, by omega⟩))

theorem sourcePanel317Remaining_final :
    sourcePanel317Remaining 54 = sourcePanel317Candidate := by
  have hdrop : sourceMidpointArray.toList.drop 13601 = [] :=
    List.drop_eq_nil_of_le (le_of_eq sourceMidpointArray_size)
  have hlast : (sourcePanel317Checkpoint 54).2 = sourcePanel317Candidate := by
    decide +kernel
  unfold sourcePanel317Remaining
  rw [show min (256*54) 13601 = 13601 from by decide, hdrop]
  exact hlast

theorem sourcePanel317Values_eq_candidate
    (hseed : intSourceTrigSeed (635/8000) = sourcePanel317Seed)
    (hc : ∀ i : Fin 54, sourcePanel317ChunkCheck i) :
    intSourceCoefficientValues (635/200) sourcePiMidpoint sourceMidpointArray.toList =
      sourcePanel317Candidate := by
  have hzero : sourcePanel317Checkpoint 0 =
      (((sourceCoefficientScale:ℤ),0), List.replicate 65 0) := by decide +kernel
  have hstart : intSourceCoefficientValues (635/200) sourcePiMidpoint
      sourceMidpointArray.toList = sourcePanel317Remaining 0 := by
    unfold intSourceCoefficientValues sourcePanel317Remaining
    rw [show (635/200:ℚ)/40 = 635/8000 from by norm_num, hseed, hzero]
    simp only [Nat.mul_zero, Nat.zero_min, List.drop_zero]
  exact hstart.trans ((sourcePanel317Remaining_all hc 54 (by omega)).trans
    sourcePanel317Remaining_final)

end ReciprocalXi

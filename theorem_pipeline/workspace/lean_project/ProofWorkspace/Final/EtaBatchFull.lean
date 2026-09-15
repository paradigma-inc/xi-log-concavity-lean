import ProofWorkspace.Final.EtaInitialStatesFull

set_option autoImplicit false
namespace ReciprocalXi

def etaStreamBatch (weights : List ℚ) : ℕ → List RoundedRootState →
    List (ℤ × ℤ) × List RoundedRootState
  | 0, states => ([], states)
  | n+1, states =>
    let next := etaStreamBatch weights n (states.map (roundedRootStep rootCertificateScale))
    ((etaStreamLowerSum weights states, etaStreamUpperSum weights states)::next.1, next.2)

theorem etaStreamBatch_final (weights : List ℚ) (n : ℕ) (states : List RoundedRootState) :
    (etaStreamBatch weights n states).2 = roundedRootTableAdvance rootCertificateScale n states := by
  induction n generalizing states with
  | zero => rfl
  | succ n ih =>
    simp only [etaStreamBatch, ih, roundedRootTableAdvance, Function.iterate_succ_apply]

theorem etaStreamBatch_length (weights : List ℚ) (n : ℕ) (states : List RoundedRootState) :
    (etaStreamBatch weights n states).1.length = n := by
  induction n generalizing states with
  | zero => rfl
  | succ n ih => simp only [etaStreamBatch, List.length_cons, ih]

theorem etaStreamBatch_getElem (N k n j : ℕ) (hj : j < n) :
    (etaStreamBatch (etaSignedWeightTable N) n (etaRootStateTable N k)).1[j]'(by
      rw [etaStreamBatch_length]; exact hj) =
      (etaStreamLowerSum (etaSignedWeightTable N) (etaRootStateTable N (k+j)),
        etaStreamUpperSum (etaSignedWeightTable N) (etaRootStateTable N (k+j))) := by
  induction n generalizing k j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [etaStreamBatch]
    | succ j =>
      simp only [etaStreamBatch, List.getElem_cons_succ, etaRootStateTable_next]
      have h := ih (k+1) j (by omega)
      simpa only [Nat.add_right_comm k 1 j] using h

theorem etaStreamBatch_final_canonical (N k n : ℕ) :
    (etaStreamBatch (etaSignedWeightTable N) n (etaRootStateTable N k)).2 =
      etaRootStateTable N (k+n) := by
  rw [etaStreamBatch_final, etaRootStateTable_advance]

end ReciprocalXi

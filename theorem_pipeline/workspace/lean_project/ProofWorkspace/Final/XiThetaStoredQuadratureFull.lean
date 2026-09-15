import ProofWorkspace.Final.XiThetaDyadicIntegralFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def theta48StoredQuadrature (v : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8, v j i

theorem theta48StoredQuadrature_error (v : ℕ → ℕ → ℝ)
    (hv : ∀ j : ℕ, j<4 → ∀ i : ℕ, i<8 →
      |theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40-
        v j i|≤320/(10:ℝ)^25) :
    |theta48Quadrature40-theta48StoredQuadrature v|≤10240/(10:ℝ)^25 := by
  unfold theta48Quadrature40 theta48StoredQuadrature
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8,
      |theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40-v j i| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun j hj ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _j ∈ Finset.range 4, ∑ _i ∈ Finset.range 8, 320/(10:ℝ)^25 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact hv j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
    _ = _ := by norm_num

theorem F48_storedQuadrature_error (v : ℕ → ℕ → ℝ)
    (hv : ∀ j : ℕ, j<4 → ∀ i : ℕ, i<8 →
      |theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40-
        v j i|≤320/(10:ℝ)^25) :
    |(F (48:ℂ)).re-(1-(2305/4:ℝ)*theta48StoredQuadrature v)/8|≤3/(10:ℝ)^16 := by
  have hq := theta48StoredQuadrature_error v hv
  have hf := F48_theta48Quadrature40_error
  have ht := abs_sub_le (F (48:ℂ)).re ((1-(2305/4:ℝ)*theta48Quadrature40)/8)
    ((1-(2305/4:ℝ)*theta48StoredQuadrature v)/8)
  have he : (1-(2305/4:ℝ)*theta48Quadrature40)/8-
      (1-(2305/4:ℝ)*theta48StoredQuadrature v)/8=
      -(2305/32:ℝ)*(theta48Quadrature40-theta48StoredQuadrature v) := by ring
  rw [he,abs_mul] at ht
  norm_num at ht
  linarith

end ReciprocalXi

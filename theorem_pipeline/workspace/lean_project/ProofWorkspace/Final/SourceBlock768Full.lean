import ProofWorkspace.Final.SourceBlock736Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock768DataFull
import ProofWorkspace.Final.EtaBlock768Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock768XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (768+k) (sourceBlock768PiPairs.getD k (0,0))
    (sourceEtaBatch768Lower k, sourceEtaBatch768Upper k)
    (sourceBlock768TwoPairs.getD k (0,0))

theorem sourceBlock768Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock768XiPair k).1:ℝ) ≤ (xi (xiGridArgument (768+k):ℂ)).re ∧
      (xi (xiGridArgument (768+k):ℂ)).re ≤ ((sourceBlock768XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (768+k) _ _ _
    (sourceBlock768PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch768_actual_enclosure k hk)
    (sourceBlock768TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock768Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock768XiPair k).1 := by
  decide +kernel

theorem sourceBlock768Reciprocal_check : ∀ k : Fin 32,
    sourceBlock768Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock768XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock768XiPair k)).2 ≤
      sourceBlock768Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block768_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((768+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (768+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock768Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (768+k) (sourceBlock768XiPair k) _
    (sourceBlock768Xi_enclosure k hk) (sourceBlock768Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock768Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first800_bound (k : ℕ) (hk : k < 800) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 768
  · exact sourceRoundedMidpoint_first768_bound k h
  · have hsum : 768+(k-768) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block768_bound (k-768) (by omega)

end ReciprocalXi

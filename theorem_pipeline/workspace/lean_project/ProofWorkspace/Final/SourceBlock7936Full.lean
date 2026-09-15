import ProofWorkspace.Final.SourceBlock7904Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7936DataFull
import ProofWorkspace.Final.EtaBlock7936Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7936XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7936+k) (sourceBlock7936PiPairs.getD k (0,0))
    (sourceEtaBatch7936Lower k, sourceEtaBatch7936Upper k)
    (sourceBlock7936TwoPairs.getD k (0,0))

theorem sourceBlock7936Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7936XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7936+k):ℂ)).re ∧
      (xi (xiGridArgument (7936+k):ℂ)).re ≤ ((sourceBlock7936XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7936+k) _ _ _
    (sourceBlock7936PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7936_actual_enclosure k hk)
    (sourceBlock7936TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7936Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7936XiPair k).1 := by
  decide +kernel

theorem sourceBlock7936Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7936Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7936XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7936XiPair k)).2 ≤
      sourceBlock7936Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7936_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7936+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7936+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7936Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7936+k) (sourceBlock7936XiPair k) _
    (sourceBlock7936Xi_enclosure k hk) (sourceBlock7936Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7936Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7968_bound (k : ℕ) (hk : k < 7968) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7936
  · exact sourceRoundedMidpoint_first7936_bound k h
  · have hsum : 7936+(k-7936) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7936_bound (k-7936) (by omega)

end ReciprocalXi

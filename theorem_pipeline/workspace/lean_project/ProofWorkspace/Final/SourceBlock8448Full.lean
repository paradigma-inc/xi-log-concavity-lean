import ProofWorkspace.Final.SourceBlock8416Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8448DataFull
import ProofWorkspace.Final.EtaBlock8448Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8448XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8448+k) (sourceBlock8448PiPairs.getD k (0,0))
    (sourceEtaBatch8448Lower k, sourceEtaBatch8448Upper k)
    (sourceBlock8448TwoPairs.getD k (0,0))

theorem sourceBlock8448Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8448XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8448+k):ℂ)).re ∧
      (xi (xiGridArgument (8448+k):ℂ)).re ≤ ((sourceBlock8448XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8448+k) _ _ _
    (sourceBlock8448PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8448_actual_enclosure k hk)
    (sourceBlock8448TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8448Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8448XiPair k).1 := by
  decide +kernel

theorem sourceBlock8448Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8448Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8448XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8448XiPair k)).2 ≤
      sourceBlock8448Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8448_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8448+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8448+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8448Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8448+k) (sourceBlock8448XiPair k) _
    (sourceBlock8448Xi_enclosure k hk) (sourceBlock8448Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8448Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8480_bound (k : ℕ) (hk : k < 8480) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8448
  · exact sourceRoundedMidpoint_first8448_bound k h
  · have hsum : 8448+(k-8448) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8448_bound (k-8448) (by omega)

end ReciprocalXi

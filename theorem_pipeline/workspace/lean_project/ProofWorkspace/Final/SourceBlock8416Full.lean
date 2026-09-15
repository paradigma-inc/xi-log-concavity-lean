import ProofWorkspace.Final.SourceBlock8384Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8416DataFull
import ProofWorkspace.Final.EtaBlock8416Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8416XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8416+k) (sourceBlock8416PiPairs.getD k (0,0))
    (sourceEtaBatch8416Lower k, sourceEtaBatch8416Upper k)
    (sourceBlock8416TwoPairs.getD k (0,0))

theorem sourceBlock8416Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8416XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8416+k):ℂ)).re ∧
      (xi (xiGridArgument (8416+k):ℂ)).re ≤ ((sourceBlock8416XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8416+k) _ _ _
    (sourceBlock8416PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8416_actual_enclosure k hk)
    (sourceBlock8416TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8416Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8416XiPair k).1 := by
  decide +kernel

theorem sourceBlock8416Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8416Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8416XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8416XiPair k)).2 ≤
      sourceBlock8416Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8416_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8416+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8416+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8416Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8416+k) (sourceBlock8416XiPair k) _
    (sourceBlock8416Xi_enclosure k hk) (sourceBlock8416Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8416Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8448_bound (k : ℕ) (hk : k < 8448) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8416
  · exact sourceRoundedMidpoint_first8416_bound k h
  · have hsum : 8416+(k-8416) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8416_bound (k-8416) (by omega)

end ReciprocalXi

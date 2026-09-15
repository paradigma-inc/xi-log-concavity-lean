import ProofWorkspace.Final.SourceBlock8256Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8288DataFull
import ProofWorkspace.Final.EtaBlock8288Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8288XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8288+k) (sourceBlock8288PiPairs.getD k (0,0))
    (sourceEtaBatch8288Lower k, sourceEtaBatch8288Upper k)
    (sourceBlock8288TwoPairs.getD k (0,0))

theorem sourceBlock8288Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8288XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8288+k):ℂ)).re ∧
      (xi (xiGridArgument (8288+k):ℂ)).re ≤ ((sourceBlock8288XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8288+k) _ _ _
    (sourceBlock8288PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8288_actual_enclosure k hk)
    (sourceBlock8288TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8288Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8288XiPair k).1 := by
  decide +kernel

theorem sourceBlock8288Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8288Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8288XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8288XiPair k)).2 ≤
      sourceBlock8288Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8288_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8288+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8288+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8288Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8288+k) (sourceBlock8288XiPair k) _
    (sourceBlock8288Xi_enclosure k hk) (sourceBlock8288Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8288Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8320_bound (k : ℕ) (hk : k < 8320) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8288
  · exact sourceRoundedMidpoint_first8288_bound k h
  · have hsum : 8288+(k-8288) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8288_bound (k-8288) (by omega)

end ReciprocalXi

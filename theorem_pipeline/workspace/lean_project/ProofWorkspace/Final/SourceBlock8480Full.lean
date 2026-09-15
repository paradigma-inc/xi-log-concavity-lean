import ProofWorkspace.Final.SourceBlock8448Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8480DataFull
import ProofWorkspace.Final.EtaBlock8480Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8480XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8480+k) (sourceBlock8480PiPairs.getD k (0,0))
    (sourceEtaBatch8480Lower k, sourceEtaBatch8480Upper k)
    (sourceBlock8480TwoPairs.getD k (0,0))

theorem sourceBlock8480Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8480XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8480+k):ℂ)).re ∧
      (xi (xiGridArgument (8480+k):ℂ)).re ≤ ((sourceBlock8480XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8480+k) _ _ _
    (sourceBlock8480PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8480_actual_enclosure k hk)
    (sourceBlock8480TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8480Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8480XiPair k).1 := by
  decide +kernel

theorem sourceBlock8480Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8480Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8480XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8480XiPair k)).2 ≤
      sourceBlock8480Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8480_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8480+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8480+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8480Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8480+k) (sourceBlock8480XiPair k) _
    (sourceBlock8480Xi_enclosure k hk) (sourceBlock8480Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8480Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8512_bound (k : ℕ) (hk : k < 8512) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8480
  · exact sourceRoundedMidpoint_first8480_bound k h
  · have hsum : 8480+(k-8480) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8480_bound (k-8480) (by omega)

end ReciprocalXi

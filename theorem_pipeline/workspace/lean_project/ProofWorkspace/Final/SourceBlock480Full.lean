import ProofWorkspace.Final.SourceBlock448Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock480DataFull
import ProofWorkspace.Final.EtaBlock480Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock480XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (480+k) (sourceBlock480PiPairs.getD k (0,0))
    (sourceEtaBatch480Lower k, sourceEtaBatch480Upper k)
    (sourceBlock480TwoPairs.getD k (0,0))

theorem sourceBlock480Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock480XiPair k).1:ℝ) ≤ (xi (xiGridArgument (480+k):ℂ)).re ∧
      (xi (xiGridArgument (480+k):ℂ)).re ≤ ((sourceBlock480XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (480+k) _ _ _
    (sourceBlock480PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch480_actual_enclosure k hk)
    (sourceBlock480TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock480Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock480XiPair k).1 := by
  decide +kernel

theorem sourceBlock480Reciprocal_check : ∀ k : Fin 32,
    sourceBlock480Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock480XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock480XiPair k)).2 ≤
      sourceBlock480Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block480_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((480+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (480+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock480Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (480+k) (sourceBlock480XiPair k) _
    (sourceBlock480Xi_enclosure k hk) (sourceBlock480Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock480Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first512_bound (k : ℕ) (hk : k < 512) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 480
  · exact sourceRoundedMidpoint_first480_bound k h
  · have hsum : 480+(k-480) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block480_bound (k-480) (by omega)

end ReciprocalXi

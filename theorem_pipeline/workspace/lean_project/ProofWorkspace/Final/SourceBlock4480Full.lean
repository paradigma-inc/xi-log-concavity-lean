import ProofWorkspace.Final.SourceBlock4448Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4480DataFull
import ProofWorkspace.Final.EtaBlock4480Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4480XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4480+k) (sourceBlock4480PiPairs.getD k (0,0))
    (sourceEtaBatch4480Lower k, sourceEtaBatch4480Upper k)
    (sourceBlock4480TwoPairs.getD k (0,0))

theorem sourceBlock4480Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4480XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4480+k):ℂ)).re ∧
      (xi (xiGridArgument (4480+k):ℂ)).re ≤ ((sourceBlock4480XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4480+k) _ _ _
    (sourceBlock4480PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4480_actual_enclosure k hk)
    (sourceBlock4480TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4480Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4480XiPair k).1 := by
  decide +kernel

theorem sourceBlock4480Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4480Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4480XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4480XiPair k)).2 ≤
      sourceBlock4480Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4480_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4480+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4480+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4480Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4480+k) (sourceBlock4480XiPair k) _
    (sourceBlock4480Xi_enclosure k hk) (sourceBlock4480Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4480Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4512_bound (k : ℕ) (hk : k < 4512) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4480
  · exact sourceRoundedMidpoint_first4480_bound k h
  · have hsum : 4480+(k-4480) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4480_bound (k-4480) (by omega)

end ReciprocalXi

import ProofWorkspace.Final.SourceBlock12448Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12480DataFull
import ProofWorkspace.Final.EtaBlock12480Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12480XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12480+k) (sourceBlock12480PiPairs.getD k (0,0))
    (sourceEtaBatch12480Lower k, sourceEtaBatch12480Upper k)
    (sourceBlock12480TwoPairs.getD k (0,0))

theorem sourceBlock12480Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12480XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12480+k):ℂ)).re ∧
      (xi (xiGridArgument (12480+k):ℂ)).re ≤ ((sourceBlock12480XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12480+k) _ _ _
    (sourceBlock12480PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12480_actual_enclosure k hk)
    (sourceBlock12480TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12480Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12480XiPair k).1 := by
  decide +kernel

theorem sourceBlock12480Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12480Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12480XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12480XiPair k)).2 ≤
      sourceBlock12480Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12480_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12480+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12480+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12480Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12480+k) (sourceBlock12480XiPair k) _
    (sourceBlock12480Xi_enclosure k hk) (sourceBlock12480Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12480Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12512_bound (k : ℕ) (hk : k < 12512) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12480
  · exact sourceRoundedMidpoint_first12480_bound k h
  · have hsum : 12480+(k-12480) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12480_bound (k-12480) (by omega)

end ReciprocalXi

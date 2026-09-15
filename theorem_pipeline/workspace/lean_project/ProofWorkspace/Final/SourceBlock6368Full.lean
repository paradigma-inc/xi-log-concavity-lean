import ProofWorkspace.Final.SourceBlock6336Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6368DataFull
import ProofWorkspace.Final.EtaBlock6368Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6368XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6368+k) (sourceBlock6368PiPairs.getD k (0,0))
    (sourceEtaBatch6368Lower k, sourceEtaBatch6368Upper k)
    (sourceBlock6368TwoPairs.getD k (0,0))

theorem sourceBlock6368Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6368XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6368+k):ℂ)).re ∧
      (xi (xiGridArgument (6368+k):ℂ)).re ≤ ((sourceBlock6368XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6368+k) _ _ _
    (sourceBlock6368PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6368_actual_enclosure k hk)
    (sourceBlock6368TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6368Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6368XiPair k).1 := by
  decide +kernel

theorem sourceBlock6368Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6368Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6368XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6368XiPair k)).2 ≤
      sourceBlock6368Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6368_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6368+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6368+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6368Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6368+k) (sourceBlock6368XiPair k) _
    (sourceBlock6368Xi_enclosure k hk) (sourceBlock6368Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6368Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6400_bound (k : ℕ) (hk : k < 6400) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6368
  · exact sourceRoundedMidpoint_first6368_bound k h
  · have hsum : 6368+(k-6368) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6368_bound (k-6368) (by omega)

end ReciprocalXi

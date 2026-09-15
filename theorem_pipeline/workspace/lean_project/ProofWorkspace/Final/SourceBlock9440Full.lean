import ProofWorkspace.Final.SourceBlock9408Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9440DataFull
import ProofWorkspace.Final.EtaBlock9440Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9440XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9440+k) (sourceBlock9440PiPairs.getD k (0,0))
    (sourceEtaBatch9440Lower k, sourceEtaBatch9440Upper k)
    (sourceBlock9440TwoPairs.getD k (0,0))

theorem sourceBlock9440Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9440XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9440+k):ℂ)).re ∧
      (xi (xiGridArgument (9440+k):ℂ)).re ≤ ((sourceBlock9440XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9440+k) _ _ _
    (sourceBlock9440PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9440_actual_enclosure k hk)
    (sourceBlock9440TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9440Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9440XiPair k).1 := by
  decide +kernel

theorem sourceBlock9440Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9440Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9440XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9440XiPair k)).2 ≤
      sourceBlock9440Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9440_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9440+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9440+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9440Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9440+k) (sourceBlock9440XiPair k) _
    (sourceBlock9440Xi_enclosure k hk) (sourceBlock9440Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9440Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9472_bound (k : ℕ) (hk : k < 9472) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9440
  · exact sourceRoundedMidpoint_first9440_bound k h
  · have hsum : 9440+(k-9440) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9440_bound (k-9440) (by omega)

end ReciprocalXi

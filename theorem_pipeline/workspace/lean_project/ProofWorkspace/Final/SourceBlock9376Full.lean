import ProofWorkspace.Final.SourceBlock9344Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9376DataFull
import ProofWorkspace.Final.EtaBlock9376Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9376XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9376+k) (sourceBlock9376PiPairs.getD k (0,0))
    (sourceEtaBatch9376Lower k, sourceEtaBatch9376Upper k)
    (sourceBlock9376TwoPairs.getD k (0,0))

theorem sourceBlock9376Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9376XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9376+k):ℂ)).re ∧
      (xi (xiGridArgument (9376+k):ℂ)).re ≤ ((sourceBlock9376XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9376+k) _ _ _
    (sourceBlock9376PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9376_actual_enclosure k hk)
    (sourceBlock9376TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9376Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9376XiPair k).1 := by
  decide +kernel

theorem sourceBlock9376Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9376Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9376XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9376XiPair k)).2 ≤
      sourceBlock9376Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9376_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9376+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9376+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9376Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9376+k) (sourceBlock9376XiPair k) _
    (sourceBlock9376Xi_enclosure k hk) (sourceBlock9376Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9376Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9408_bound (k : ℕ) (hk : k < 9408) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9376
  · exact sourceRoundedMidpoint_first9376_bound k h
  · have hsum : 9376+(k-9376) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9376_bound (k-9376) (by omega)

end ReciprocalXi

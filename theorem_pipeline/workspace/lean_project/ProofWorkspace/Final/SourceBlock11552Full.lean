import ProofWorkspace.Final.SourceBlock11520Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11552DataFull
import ProofWorkspace.Final.EtaBlock11552Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11552XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11552+k) (sourceBlock11552PiPairs.getD k (0,0))
    (sourceEtaBatch11552Lower k, sourceEtaBatch11552Upper k)
    (sourceBlock11552TwoPairs.getD k (0,0))

theorem sourceBlock11552Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11552XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11552+k):ℂ)).re ∧
      (xi (xiGridArgument (11552+k):ℂ)).re ≤ ((sourceBlock11552XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11552+k) _ _ _
    (sourceBlock11552PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11552_actual_enclosure k hk)
    (sourceBlock11552TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11552Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11552XiPair k).1 := by
  decide +kernel

theorem sourceBlock11552Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11552Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11552XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11552XiPair k)).2 ≤
      sourceBlock11552Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11552_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11552+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11552+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11552Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11552+k) (sourceBlock11552XiPair k) _
    (sourceBlock11552Xi_enclosure k hk) (sourceBlock11552Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11552Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11584_bound (k : ℕ) (hk : k < 11584) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11552
  · exact sourceRoundedMidpoint_first11552_bound k h
  · have hsum : 11552+(k-11552) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11552_bound (k-11552) (by omega)

end ReciprocalXi

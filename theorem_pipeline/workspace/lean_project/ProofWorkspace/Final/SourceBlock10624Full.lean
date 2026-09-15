import ProofWorkspace.Final.SourceBlock10592Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10624DataFull
import ProofWorkspace.Final.EtaBlock10624Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10624XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10624+k) (sourceBlock10624PiPairs.getD k (0,0))
    (sourceEtaBatch10624Lower k, sourceEtaBatch10624Upper k)
    (sourceBlock10624TwoPairs.getD k (0,0))

theorem sourceBlock10624Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10624XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10624+k):ℂ)).re ∧
      (xi (xiGridArgument (10624+k):ℂ)).re ≤ ((sourceBlock10624XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10624+k) _ _ _
    (sourceBlock10624PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10624_actual_enclosure k hk)
    (sourceBlock10624TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10624Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10624XiPair k).1 := by
  decide +kernel

theorem sourceBlock10624Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10624Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10624XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10624XiPair k)).2 ≤
      sourceBlock10624Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10624_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10624+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10624+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10624Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10624+k) (sourceBlock10624XiPair k) _
    (sourceBlock10624Xi_enclosure k hk) (sourceBlock10624Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10624Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10656_bound (k : ℕ) (hk : k < 10656) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10624
  · exact sourceRoundedMidpoint_first10624_bound k h
  · have hsum : 10624+(k-10624) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10624_bound (k-10624) (by omega)

end ReciprocalXi

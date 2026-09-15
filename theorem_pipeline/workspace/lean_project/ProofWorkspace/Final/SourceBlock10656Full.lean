import ProofWorkspace.Final.SourceBlock10624Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10656DataFull
import ProofWorkspace.Final.EtaBlock10656Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10656XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10656+k) (sourceBlock10656PiPairs.getD k (0,0))
    (sourceEtaBatch10656Lower k, sourceEtaBatch10656Upper k)
    (sourceBlock10656TwoPairs.getD k (0,0))

theorem sourceBlock10656Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10656XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10656+k):ℂ)).re ∧
      (xi (xiGridArgument (10656+k):ℂ)).re ≤ ((sourceBlock10656XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10656+k) _ _ _
    (sourceBlock10656PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10656_actual_enclosure k hk)
    (sourceBlock10656TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10656Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10656XiPair k).1 := by
  decide +kernel

theorem sourceBlock10656Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10656Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10656XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10656XiPair k)).2 ≤
      sourceBlock10656Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10656_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10656+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10656+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10656Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10656+k) (sourceBlock10656XiPair k) _
    (sourceBlock10656Xi_enclosure k hk) (sourceBlock10656Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10656Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10688_bound (k : ℕ) (hk : k < 10688) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10656
  · exact sourceRoundedMidpoint_first10656_bound k h
  · have hsum : 10656+(k-10656) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10656_bound (k-10656) (by omega)

end ReciprocalXi

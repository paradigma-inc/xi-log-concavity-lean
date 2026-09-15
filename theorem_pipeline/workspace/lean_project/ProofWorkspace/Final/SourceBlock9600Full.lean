import ProofWorkspace.Final.SourceBlock9568Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9600DataFull
import ProofWorkspace.Final.EtaBlock9600Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9600XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9600+k) (sourceBlock9600PiPairs.getD k (0,0))
    (sourceEtaBatch9600Lower k, sourceEtaBatch9600Upper k)
    (sourceBlock9600TwoPairs.getD k (0,0))

theorem sourceBlock9600Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9600XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9600+k):ℂ)).re ∧
      (xi (xiGridArgument (9600+k):ℂ)).re ≤ ((sourceBlock9600XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9600+k) _ _ _
    (sourceBlock9600PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9600_actual_enclosure k hk)
    (sourceBlock9600TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9600Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9600XiPair k).1 := by
  decide +kernel

theorem sourceBlock9600Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9600Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9600XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9600XiPair k)).2 ≤
      sourceBlock9600Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9600_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9600+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9600+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9600Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9600+k) (sourceBlock9600XiPair k) _
    (sourceBlock9600Xi_enclosure k hk) (sourceBlock9600Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9600Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9632_bound (k : ℕ) (hk : k < 9632) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9600
  · exact sourceRoundedMidpoint_first9600_bound k h
  · have hsum : 9600+(k-9600) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9600_bound (k-9600) (by omega)

end ReciprocalXi

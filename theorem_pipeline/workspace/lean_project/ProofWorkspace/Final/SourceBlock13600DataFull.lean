import ProofWorkspace.Final.SourceMidpointSliceFull
import ProofWorkspace.Final.SourceBlock13568DataFull
import ProofWorkspace.Final.SourcePowerTableFull
import ProofWorkspace.Final.SourceMidpointArrayFull
import ProofWorkspace.Final.RetainedRootEvaluatorFull

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace ReciprocalXi

def sourceBlock13600PiPairs : List (ℚ × ℚ) := [
  ((414928582919361561305526875025652977048108602046875702867477877935229250554171127324469177796157860663003183706663467647439736253224533710:ℚ)/(10:ℚ)^180, (414928582919361561305526875025652977048108602046875702867477877935229250554171127324469177796157860663003183706663467647439736253224533850:ℚ)/(10:ℚ)^180)
]

def sourceBlock13600TwoPairs : List (ℚ × ℚ) := [
  ((472482512755572079134572347421237940432905774256707247219388368283401883162256313413449997423846005799981327108838683853724878454:ℚ)/(10:ℚ)^180, (472482512755572079134572347421237940432905774256707247219388368283401883162256313413449997423846005799981327108838683853724878570:ℚ)/(10:ℚ)^180)
]

def sourceBlock13600Midpoints : List ℚ := [
  (1649662999074119019779662767675790336345616537753973166638302163389134606028220733476180299551870618384578072464352488494059850535503522727413282850572960763189:ℚ)/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
]

theorem sourceBlock13600PiPairs_eq : ∀ k : Fin 1,
    (retainedPiLower (13600+k), retainedPiUpper (13600+k)) =
      sourceBlock13600PiPairs.getD k (0,0) := by
  have hfirst : (retainedPiLower 13600, retainedPiUpper 13600) =
      sourceBlock13600PiPairs.getD 0 (0,0) := calc
    _ = sourcePowerPairStep sourcePiRootLower sourcePiRootUpper
        (retainedPiLower 13599, retainedPiUpper 13599) :=
      retainedPiPair_succ 13599
    _ = sourcePowerPairStep sourcePiRootLower sourcePiRootUpper (sourceBlock13568PiPairs.getD 31 (0,0)) :=
      congrArg (sourcePowerPairStep sourcePiRootLower sourcePiRootUpper) (sourceBlock13568PiPairs_eq ⟨31, by decide⟩)
    _ = sourceBlock13600PiPairs.getD 0 (0,0) := by decide +kernel
  have hnext : ∀ k : Fin 0,
      sourceBlock13600PiPairs.getD (k+1) (0,0) =
        sourcePowerPairStep sourcePiRootLower sourcePiRootUpper (sourceBlock13600PiPairs.getD k (0,0)) := by
    decide +kernel
  intro k
  exact sourcePowerTable_sound
    (fun j => (retainedPiLower j, retainedPiUpper j))
    (sourcePowerPairStep sourcePiRootLower sourcePiRootUpper) retainedPiPair_succ 13600 1 sourceBlock13600PiPairs
    hfirst (fun j hj => hnext ⟨j, by omega⟩) k k.isLt

theorem sourceBlock13600TwoPairs_eq : ∀ k : Fin 1,
    (retainedTwoLower (13600+k), retainedTwoUpper (13600+k)) =
      sourceBlock13600TwoPairs.getD k (0,0) := by
  have hfirst : (retainedTwoLower 13600, retainedTwoUpper 13600) =
      sourceBlock13600TwoPairs.getD 0 (0,0) := calc
    _ = sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2)
        (retainedTwoLower 13599, retainedTwoUpper 13599) :=
      retainedTwoPair_succ 13599
    _ = sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2) (sourceBlock13568TwoPairs.getD 31 (0,0)) :=
      congrArg (sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2)) (sourceBlock13568TwoPairs_eq ⟨31, by decide⟩)
    _ = sourceBlock13600TwoPairs.getD 0 (0,0) := by decide +kernel
  have hnext : ∀ k : Fin 0,
      sourceBlock13600TwoPairs.getD (k+1) (0,0) =
        sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2) (sourceBlock13600TwoPairs.getD k (0,0)) := by
    decide +kernel
  intro k
  exact sourcePowerTable_sound
    (fun j => (retainedTwoLower j, retainedTwoUpper j))
    (sourcePowerPairStep (rootLowerFor 2) (rootUpperFor 2)) retainedTwoPair_succ 13600 1 sourceBlock13600TwoPairs
    hfirst (fun j hj => hnext ⟨j, by omega⟩) k k.isLt

theorem sourceBlock13600Midpoints_slice_checked :
    sourceBlock13600Midpoints = (sourceMidpointArray.toList.drop 13600).take 1 := by
  decide +kernel

theorem sourceBlock13600Midpoints_eq_array : ∀ k : Fin 1,
    sourceBlock13600Midpoints.getD k 0 = sourceRoundedMidpoint (13600+k) := by
  intro k
  exact sourceMidpointSlice_lookup 13600 1 sourceBlock13600Midpoints
    sourceBlock13600Midpoints_slice_checked k k.isLt

end ReciprocalXi

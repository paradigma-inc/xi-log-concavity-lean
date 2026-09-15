import ProofWorkspace.Final.FirstSourceCandidateArithmeticFull
import ProofWorkspace.Final.FirstSourceEtaLiteralsFull
import ProofWorkspace.Final.GammaFirstNodeLiteralsFull

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

namespace ReciprocalXi


/-- The k=1 midpoint obtained by replaying the source script's
160-significant-digit ROUND_HALF_EVEN `mid` operation on the JSONL interval. -/
def sourceNodeOneRoundedMidpoint : ℚ :=
  (999996389851796083394662141260750674189357763336316000509937461316013207351621073024621156252582430239232053337666193634179227937882778772263951315429916000352 : ℚ) /
    (10 : ℚ) ^ 159

theorem sourceNodeOneRoundedMidpoint_minus_exact :
    sourceNodeOneRoundedMidpoint - sourceNodeOneMidpoint =
      1 / (4 : ℚ) / (10 : ℚ) ^ 159 := by
  norm_num [sourceNodeOneRoundedMidpoint, sourceNodeOneMidpoint,
    sourceNodeOneLower, sourceNodeOneUpper]

theorem candidateReciprocalOne_precision_rounded :
    sourceNodeOneRoundedMidpoint - 2/(10:ℚ)^120 ≤ candidateReciprocalOne.1 ∧
      candidateReciprocalOne.2 ≤
        sourceNodeOneRoundedMidpoint + 2/(10:ℚ)^120 := by
  rw [candidateReciprocalOne_literals]
  decide +kernel


theorem candidateGammaZero_eq_grid
    (h : (ratLogGammaFastLower (1/4) 440 480 400 (10^180),
      ratLogGammaFastUpper (1/4) 440 480 400 (10^180)) =
      (candidateGammaNodeZeroLower, candidateGammaNodeZeroUpper)) :
    (ratGammaGridFastLower 0 440 480 400 256 128 (10^180),
      ratGammaGridFastUpper 0 440 480 400 256 128 (10^180)) = candidateGammaZero := by
  have hl := congrArg Prod.fst h
  have hu := congrArg Prod.snd h
  dsimp only at hl hu
  unfold ratGammaGridFastLower ratGammaGridFastUpper ratGammaFastLower ratGammaFastUpper
  have hoff : gammaGridOffset 0 = (1/4:ℚ) := by norm_num [gammaGridOffset, gammaGridArgument]
  have hmul : gammaGridMultiplier 0 = (4:ℚ) := by norm_num [gammaGridMultiplier, gammaGridArgument]
  rw [hoff, hmul, hl, hu]
  unfold candidateGammaZero
  rw [ratExpScanIntegerLower_eq _ _ _ _ (by norm_num),
    ratExpScanIntegerUpper_eq _ _ _ _ (by norm_num)]
  congr 2 <;> ring

theorem candidateGammaOne_eq_grid
    (h : (ratLogGammaFastLower (41/160) 440 480 400 (10^180),
      ratLogGammaFastUpper (41/160) 440 480 400 (10^180)) =
      (candidateGammaNodeOneLower, candidateGammaNodeOneUpper)) :
    (ratGammaGridFastLower 1 440 480 400 256 128 (10^180),
      ratGammaGridFastUpper 1 440 480 400 256 128 (10^180)) = candidateGammaOne := by
  have hl := congrArg Prod.fst h
  have hu := congrArg Prod.snd h
  dsimp only at hl hu
  unfold ratGammaGridFastLower ratGammaGridFastUpper ratGammaFastLower ratGammaFastUpper
  have hoff : gammaGridOffset 1 = (41/160:ℚ) := by norm_num [gammaGridOffset, gammaGridArgument]
  have hmul : gammaGridMultiplier 1 = (160/41:ℚ) := by norm_num [gammaGridMultiplier, gammaGridArgument]
  rw [hoff, hmul, hl, hu]
  unfold candidateGammaOne
  rw [ratExpScanIntegerLower_eq _ _ _ _ (by norm_num),
    ratExpScanIntegerUpper_eq _ _ _ _ (by norm_num)]
  congr 2 <;> ring

theorem candidateEtaZero_eq_grid :
    (ratEtaRootGridLower 400 0 (10^180) rootLowerFor rootUpperFor,
      ratEtaRootGridUpper 400 0 (10^180) rootLowerFor rootUpperFor) =
      (candidateEtaNodeZeroLower, candidateEtaNodeZeroUpper) := by
  rw [←ratEtaRootTableLower_eq, ←ratEtaRootTableUpper_eq, etaNodeZero_literals]
  rfl

theorem candidateEtaOne_eq_grid :
    (ratEtaRootGridLower 400 1 (10^180) rootLowerFor rootUpperFor,
      ratEtaRootGridUpper 400 1 (10^180) rootLowerFor rootUpperFor) =
      (candidateEtaNodeOneLower, candidateEtaNodeOneUpper) := by
  rw [←ratEtaRootTableLower_eq, ←ratEtaRootTableUpper_eq, etaNodeOne_literals]
  rfl

theorem candidateXiZero_eq_grid
    (hg : (ratGammaGridFastLower 0 440 480 400 256 128 (10^180),
      ratGammaGridFastUpper 0 440 480 400 256 128 (10^180)) = candidateGammaZero) :
    (ratXiRootGridLower 0 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor,
      ratXiRootGridUpper 0 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor) =
      candidateXiZero := by
  have hp := (nodePiCandidate_eq 0).symm.trans nodeZeroPi_literals
  have he := candidateEtaZero_eq_grid
  have hb := nodeZeroBracket_literals
  unfold ratXiRootGridLower ratXiRootGridUpper
  simp only [firstNodeParams, firstNodeGrid, Nat.reduceEqDiff, if_false]
  have hgl := congrArg Prod.fst hg
  have hgu := congrArg Prod.snd hg
  have hpl := congrArg Prod.fst hp
  have hpu := congrArg Prod.snd hp
  have hel := congrArg Prod.fst he
  have heu := congrArg Prod.snd he
  have hbl := congrArg Prod.fst hb
  have hbu := congrArg Prod.snd hb
  dsimp only at hgl hgu hpl hpu hel heu hbl hbu
  rw [hgl, hgu, hpl, hpu, hel, heu, hbl, hbu]
  have hgpos : 0 ≤ candidateGammaZero.1 := by
    rw [candidateGammaZero_literals]
    norm_num [candidateGammaZeroValues]
  have hppos : 0 ≤ nodeZeroPiLower := by norm_num [nodeZeroPiLower]
  have hepos : 0 ≤ candidateEtaNodeZeroLower := by norm_num [candidateEtaNodeZeroLower]
  have hbpos : 0 ≤ nodeZeroBracketLower := by norm_num [nodeZeroBracketLower]
  rw [max_eq_right hgpos, max_eq_right hppos, max_eq_right hepos, max_eq_right hbpos]
  unfold candidateXiZero
  norm_num only [xiGridArgument]

theorem candidateXiOne_eq_grid
    (hg : (ratGammaGridFastLower 1 440 480 400 256 128 (10^180),
      ratGammaGridFastUpper 1 440 480 400 256 128 (10^180)) = candidateGammaOne) :
    (ratXiRootGridLower 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor,
      ratXiRootGridUpper 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor) =
      candidateXiOne := by
  have hp := (nodePiCandidate_eq 1).symm.trans nodeOnePi_literals
  have he := candidateEtaOne_eq_grid
  have hb := nodeOneBracket_literals
  unfold ratXiRootGridLower ratXiRootGridUpper
  simp only [firstNodeParams, firstNodeGrid, Nat.reduceEqDiff, if_false]
  have hgl := congrArg Prod.fst hg
  have hgu := congrArg Prod.snd hg
  have hpl := congrArg Prod.fst hp
  have hpu := congrArg Prod.snd hp
  have hel := congrArg Prod.fst he
  have heu := congrArg Prod.snd he
  have hbl := congrArg Prod.fst hb
  have hbu := congrArg Prod.snd hb
  dsimp only at hgl hgu hpl hpu hel heu hbl hbu
  rw [hgl, hgu, hpl, hpu, hel, heu, hbl, hbu]
  have hgpos : 0 ≤ candidateGammaOne.1 := by
    rw [candidateGammaOne_literals]
    norm_num [candidateGammaOneValues]
  have hppos : 0 ≤ nodeOnePiLower := by norm_num [nodeOnePiLower]
  have hepos : 0 ≤ candidateEtaNodeOneLower := by norm_num [candidateEtaNodeOneLower]
  have hbpos : 0 ≤ nodeOneBracketLower := by norm_num [nodeOneBracketLower]
  rw [max_eq_right hgpos, max_eq_right hppos, max_eq_right hepos, max_eq_right hbpos]
  unfold candidateXiOne
  norm_num only [xiGridArgument]

theorem first_source_node_bound_of_gamma_literals (midpoint : ℚ)
    (hprecision : midpoint - 2/(10:ℚ)^120 ≤ candidateReciprocalOne.1 ∧
      candidateReciprocalOne.2 ≤ midpoint + 2/(10:ℚ)^120)
    (hzero : (ratLogGammaFastLower (1/4) 440 480 400 (10^180),
      ratLogGammaFastUpper (1/4) 440 480 400 (10^180)) =
      (candidateGammaNodeZeroLower, candidateGammaNodeZeroUpper))
    (hone : (ratLogGammaFastLower (41/160) 440 480 400 (10^180),
      ratLogGammaFastUpper (41/160) 440 480 400 (10^180)) =
      (candidateGammaNodeOneLower, candidateGammaNodeOneUpper)) :
    |(reciprocalTransform (1/40)).re - (midpoint:ℝ)| ≤ 2/(10:ℝ)^120 := by
  have hxzero := candidateXiZero_eq_grid (candidateGammaZero_eq_grid hzero)
  have hxone := candidateXiOne_eq_grid (candidateGammaOne_eq_grid hone)
  have hx0l := congrArg Prod.fst hxzero
  have hx0u := congrArg Prod.snd hxzero
  have hx1l := congrArg Prod.fst hxone
  have hx1u := congrArg Prod.snd hxone
  dsimp only at hx0l hx0u hx1l hx1u
  have hx0pos : 0 ≤ candidateXiZero.1 := by
    rw [candidateXiZero_literals]
    norm_num [candidateXiZeroValues]
  have hx1pos : 0 < candidateXiOne.1 := by
    rw [candidateXiOne_literals]
    norm_num [candidateXiOneValues]
  have hd : 0 < ratXiRootGridLower 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor := by
    rw [hx1l]
    exact hx1pos
  have hr :
      (ratReciprocalRootGridLower 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor,
        ratReciprocalRootGridUpper 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor) =
        candidateReciprocalOne := by
    unfold ratReciprocalRootGridLower ratReciprocalRootGridUpper
    rw [hx0l, hx0u, hx1l, hx1u, max_eq_right hx0pos]
    rfl
  have hrl := congrArg Prod.fst hr
  have hru := congrArg Prod.snd hr
  dsimp only at hrl hru
  have ha := ratReciprocalRootGrid_enclosure 1 firstNodeParams firstNodeGrid
    rootLowerFor rootUpperFor firstNode_zero_root_eval_checks
    (fun _ => firstNode_one_root_eval_checks) hd
  rw [hrl, hru] at ha
  norm_num only [Nat.cast_one] at ha
  have hp := hprecision
  have hl : ((midpoint - 2/(10:ℚ)^120:ℚ):ℝ) ≤
      (candidateReciprocalOne.1:ℝ) := Rat.cast_le.mpr hp.1
  have hu : (candidateReciprocalOne.2:ℝ) ≤
      ((midpoint + 2/(10:ℚ)^120:ℚ):ℝ) := Rat.cast_le.mpr hp.2
  push_cast at hl hu
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2]

theorem first_source_node_exact_midpoint_bound :
    |(reciprocalTransform (1/40)).re - (sourceNodeOneMidpoint:ℝ)| ≤ 2/(10:ℝ)^120 :=
  first_source_node_bound_of_gamma_literals sourceNodeOneMidpoint
    candidateReciprocalOne_precision gammaNodeZero_fast_literals gammaNodeOne_fast_literals

theorem first_source_node_rounded_midpoint_bound :
    |(reciprocalTransform (1/40)).re - (sourceNodeOneRoundedMidpoint:ℝ)| ≤ 2/(10:ℝ)^120 :=
  first_source_node_bound_of_gamma_literals sourceNodeOneRoundedMidpoint
    candidateReciprocalOne_precision_rounded gammaNodeZero_fast_literals gammaNodeOne_fast_literals

end ReciprocalXi



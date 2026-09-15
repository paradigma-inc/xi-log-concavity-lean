import ProofWorkspace.Final.RetainedRootEvaluatorFull

set_option autoImplicit false
namespace ReciprocalXi

def etaRootStateTable (N k : ℕ) : List RoundedRootState :=
  (List.range N).map (fun j => rootStateFor (j+1) k)

def etaSignedWeightTable (N : ℕ) : List ℚ :=
  (ratEtaWeightTable N).mapIdx (fun j w => (-1:ℚ)^j*w)

def etaStreamLowerSum (weights : List ℚ) (states : List RoundedRootState) : ℤ :=
  (List.zipWith weightedRootStateLowerTerm weights states).sum

def etaStreamUpperSum (weights : List ℚ) (states : List RoundedRootState) : ℤ :=
  (List.zipWith weightedRootStateUpperTerm weights states).sum

theorem etaRootStateTable_length (N k : ℕ) : (etaRootStateTable N k).length = N := by
  simp [etaRootStateTable]

theorem etaRootStateTable_next (N k : ℕ) :
    (etaRootStateTable N k).map (roundedRootStep rootCertificateScale) =
      etaRootStateTable N (k+1) := by
  simp only [etaRootStateTable, List.map_map]
  congr 1

theorem etaRootStateTable_advance (N k t : ℕ) :
    roundedRootTableAdvance rootCertificateScale t (etaRootStateTable N k) =
      etaRootStateTable N (k+t) := by
  induction t with
  | zero => simp [roundedRootTableAdvance]
  | succ t ih =>
    unfold roundedRootTableAdvance at ih ⊢
    rw [Function.iterate_succ_apply', ih, etaRootStateTable_next]
    simp only [Nat.add_assoc]

theorem etaStreamLowerSum_eq (N k : ℕ) :
    etaStreamLowerSum (etaSignedWeightTable N) (etaRootStateTable N k) =
      ((ratEtaWeightTable N).mapIdx (fun j w => intEtaRootLowerTerm w j k)).sum := by
  unfold etaStreamLowerSum
  congr 1
  apply List.ext_getElem
  · simp [etaSignedWeightTable, etaRootStateTable, ratEtaWeightTable_length]
  · intro j hj hj'
    simp [etaSignedWeightTable, etaRootStateTable, weightedRootStateLowerTerm_eq]

theorem etaStreamUpperSum_eq (N k : ℕ) :
    etaStreamUpperSum (etaSignedWeightTable N) (etaRootStateTable N k) =
      ((ratEtaWeightTable N).mapIdx (fun j w => intEtaRootUpperTerm w j k)).sum := by
  unfold etaStreamUpperSum
  congr 1
  apply List.ext_getElem
  · simp [etaSignedWeightTable, etaRootStateTable, ratEtaWeightTable_length]
  · intro j hj hj'
    simp [etaSignedWeightTable, etaRootStateTable, weightedRootStateUpperTerm_eq]

def ratEtaStreamLower (weights : List ℚ) (states : List RoundedRootState) : ℚ :=
  ratRoundLower ((etaStreamLowerSum weights states:ℚ)/rootCertificateScale) rootCertificateScale

def ratEtaStreamUpper (N : ℕ) (weights : List ℚ) (states : List RoundedRootState) : ℚ :=
  ratRoundUpper ((etaStreamUpperSum weights states:ℚ)/rootCertificateScale+1/2^N) rootCertificateScale

theorem ratEtaStreamLower_eq (N k : ℕ) :
    ratEtaStreamLower (etaSignedWeightTable N) (etaRootStateTable N k) =
      ratEtaRootGridLower N k rootCertificateScale rootLowerFor rootUpperFor := by
  rw [←ratEtaRootIntegerLower_eq]
  unfold ratEtaStreamLower ratEtaRootIntegerLower
  rw [etaStreamLowerSum_eq]

theorem ratEtaStreamUpper_eq (N k : ℕ) :
    ratEtaStreamUpper N (etaSignedWeightTable N) (etaRootStateTable N k) =
      ratEtaRootGridUpper N k rootCertificateScale rootLowerFor rootUpperFor := by
  rw [←ratEtaRootIntegerUpper_eq]
  unfold ratEtaStreamUpper ratEtaRootIntegerUpper
  rw [etaStreamUpperSum_eq]

theorem ratEtaStream_retained_enclosure (k : ℕ) :
    (ratEtaStreamLower (etaSignedWeightTable 400) (etaRootStateTable 400 k):ℝ) ≤
      etaIntegral (xiGridArgument k:ℝ) ∧
    etaIntegral (xiGridArgument k:ℝ) ≤
      (ratEtaStreamUpper 400 (etaSignedWeightTable 400) (etaRootStateTable 400 k):ℝ) := by
  rw [ratEtaStreamLower_eq, ratEtaStreamUpper_eq]
  exact retainedEta_enclosure k

end ReciprocalXi


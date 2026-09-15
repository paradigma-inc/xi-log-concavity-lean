import ProofWorkspace.Final.IntegerPowerArithmeticFull
import ProofWorkspace.Final.RootEtaGridBoundsFull
import ProofWorkspace.Final.RootPowerCertificateFull
set_option autoImplicit false
namespace ReciprocalXi

theorem ratRoundLower_weighted_min (w : ℚ) (l u : ℤ) (B : ℕ) (hB : 0 < B) :
    ratRoundLower (min (w*((l:ℚ)/B)) (w*((u:ℚ)/B))) B =
      (((min (w.num*l) (w.num*u) / (w.den:ℤ):ℤ):ℚ)/B) := by
  have hb : (B:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have he (a : ℤ) : (B:ℚ)*(w*((a:ℚ)/B)) = ((w.num*a:ℤ):ℚ)/w.den := by
    calc
      _ = w*(a:ℚ) := by field_simp
      _ = ((w.num:ℚ)/w.den)*(a:ℚ) :=
        congrArg (fun q : ℚ => q*(a:ℚ)) (Rat.num_div_den w).symm
      _ = _ := by push_cast; ring
  unfold ratRoundLower
  rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg B), he, he,
    min_div_div_right (Nat.cast_nonneg w.den), ←Int.cast_min,
    Int.floor_div_natCast, Int.floor_intCast]

theorem ratRoundUpper_weighted_max (w : ℚ) (l u : ℤ) (B : ℕ) (hB : 0 < B) :
    ratRoundUpper (max (w*((l:ℚ)/B)) (w*((u:ℚ)/B))) B =
      (((-(-max (w.num*l) (w.num*u) / (w.den:ℤ)):ℤ):ℚ)/B) := by
  have hb : (B:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have he (a : ℤ) : (B:ℚ)*(w*((a:ℚ)/B)) = ((w.num*a:ℤ):ℚ)/w.den := by
    calc
      _ = w*(a:ℚ) := by field_simp
      _ = ((w.num:ℚ)/w.den)*(a:ℚ) :=
        congrArg (fun q : ℚ => q*(a:ℚ)) (Rat.num_div_den w).symm
      _ = _ := by push_cast; ring
  unfold ratRoundUpper
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg B), he, he,
    max_div_div_right (Nat.cast_nonneg w.den), ←Int.cast_max]
  have hn (a : ℤ) : (a:ℚ)/w.den = -(((-a:ℤ):ℚ)/w.den) := by push_cast; ring
  rw [hn, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast, Int.cast_neg]

def rootPowIntegerLower (a n : ℕ) : ℤ :=
  intPowRoundLower (rootCertificateRows.get (rootCertificateIndex a)).l rootCertificateScale n
def rootPowIntegerUpper (a n : ℕ) : ℤ :=
  intPowRoundUpper (rootCertificateRows.get (rootCertificateIndex a)).u rootCertificateScale n

theorem rootPowIntegerLower_eq (a n : ℕ) :
    (rootPowIntegerLower a n:ℚ)/rootCertificateScale =
      ratPowRoundLower (rootLowerFor a) rootCertificateScale n := by
  simpa only [rootPowIntegerLower, rootLowerFor, rootCertificateLower, Int.cast_natCast]
    using intPowRoundLower_eq ((rootCertificateRows.get (rootCertificateIndex a)).l:ℤ)
      rootCertificateScale n (by norm_num [rootCertificateScale])
theorem rootPowIntegerUpper_eq (a n : ℕ) :
    (rootPowIntegerUpper a n:ℚ)/rootCertificateScale =
      ratPowRoundUpper (rootUpperFor a) rootCertificateScale n := by
  simpa only [rootPowIntegerUpper, rootUpperFor, rootCertificateUpper, Int.cast_natCast]
    using intPowRoundUpper_eq ((rootCertificateRows.get (rootCertificateIndex a)).u:ℤ)
      rootCertificateScale n (by norm_num [rootCertificateScale])

def intEtaRootLowerTerm (w : ℚ) (j k : ℕ) : ℤ :=
  let c := (-1:ℚ)^j*w
  min (c.num*rootPowIntegerLower (j+1) (k+40))
    (c.num*rootPowIntegerUpper (j+1) (k+40)) / (c.den:ℤ)
def intEtaRootUpperTerm (w : ℚ) (j k : ℕ) : ℤ :=
  let c := (-1:ℚ)^j*w;
  - ((- (max (c.num*rootPowIntegerLower (j+1) (k+40))
    (c.num*rootPowIntegerUpper (j+1) (k+40)))) / (c.den:ℤ))

theorem intEtaRootLowerTerm_eq (w : ℚ) (j k : ℕ) :
    (intEtaRootLowerTerm w j k:ℚ)/rootCertificateScale =
      ratRoundLower (min (((-1:ℚ)^j*w)*ratPowRoundLower (rootLowerFor (j+1)) rootCertificateScale (k+40))
        (((-1:ℚ)^j*w)*ratPowRoundUpper (rootUpperFor (j+1)) rootCertificateScale (k+40))) rootCertificateScale := by
  rw [←rootPowIntegerLower_eq, ←rootPowIntegerUpper_eq,
    ratRoundLower_weighted_min _ _ _ _ (by norm_num [rootCertificateScale])]
  rfl
theorem intEtaRootUpperTerm_eq (w : ℚ) (j k : ℕ) :
    (intEtaRootUpperTerm w j k:ℚ)/rootCertificateScale =
      ratRoundUpper (max (((-1:ℚ)^j*w)*ratPowRoundLower (rootLowerFor (j+1)) rootCertificateScale (k+40))
        (((-1:ℚ)^j*w)*ratPowRoundUpper (rootUpperFor (j+1)) rootCertificateScale (k+40))) rootCertificateScale := by
  rw [←rootPowIntegerLower_eq, ←rootPowIntegerUpper_eq,
    ratRoundUpper_weighted_max _ _ _ _ (by norm_num [rootCertificateScale])]
  rfl

def ratEtaRootIntegerLower (N k : ℕ) : ℚ :=
  ratRoundLower (((ratEtaWeightTable N).mapIdx (fun j w => intEtaRootLowerTerm w j k)).sum / (rootCertificateScale:ℚ)) rootCertificateScale
def ratEtaRootIntegerUpper (N k : ℕ) : ℚ :=
  ratRoundUpper (((ratEtaWeightTable N).mapIdx (fun j w => intEtaRootUpperTerm w j k)).sum / (rootCertificateScale:ℚ) + 1/2^N) rootCertificateScale

theorem ratEtaRootIntegerLower_eq (N k : ℕ) :
    ratEtaRootIntegerLower N k =
      ratEtaRootGridLower N k rootCertificateScale rootLowerFor rootUpperFor := by
  rw [←ratEtaRootTableLower_eq]
  unfold ratEtaRootIntegerLower ratEtaRootTableLower
  congr 1
  rw [intList_sum_div]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [intEtaRootLowerTerm_eq]

theorem ratEtaRootIntegerUpper_eq (N k : ℕ) :
    ratEtaRootIntegerUpper N k =
      ratEtaRootGridUpper N k rootCertificateScale rootLowerFor rootUpperFor := by
  rw [←ratEtaRootTableUpper_eq]
  unfold ratEtaRootIntegerUpper ratEtaRootTableUpper
  congr 2
  rw [intList_sum_div]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [intEtaRootUpperTerm_eq]
end ReciprocalXi


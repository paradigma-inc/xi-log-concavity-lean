import ProofWorkspace.Final.RationalRoundingBoundsFull
import ProofWorkspace.Final.EtaWeightTableFull

/-! Exact integer-division implementations of fixed-grid eta rounding. -/

set_option autoImplicit false

namespace ReciprocalXi

theorem ratRoundLower_intDiv (a : ℤ) (d B : ℕ) :
    ratRoundLower ((a:ℚ)/d) B = (((B:ℤ)*a/(d:ℤ):ℤ):ℚ)/B := by
  have he : (B:ℚ)*((a:ℚ)/d) = (((B:ℤ)*a:ℤ):ℚ)/d := by push_cast; ring
  unfold ratRoundLower
  rw [he, Int.floor_div_natCast, Int.floor_intCast]

theorem ratRoundUpper_intDiv (a : ℤ) (d B : ℕ) :
    ratRoundUpper ((a:ℚ)/d) B = ((-(-((B:ℤ)*a)/(d:ℤ)):ℤ):ℚ)/B := by
  have he : (B:ℚ)*((a:ℚ)/d) = -(((-((B:ℤ)*a):ℤ):ℚ)/d) := by push_cast; ring
  unfold ratRoundUpper
  rw [he, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast, Int.cast_neg]

def intEtaTermLower (w : ℚ) (j k B : ℕ) : ℤ :=
  (B:ℤ) * ((-1:ℤ)^j * w.num) / (w.den * (j+1)^k : ℕ)

def intEtaTermUpper (w : ℚ) (j k B : ℕ) : ℤ :=
  -(-((B:ℤ) * ((-1:ℤ)^j * w.num)) / (w.den * (j+1)^k : ℕ))

theorem ratEtaTerm_num_den (w : ℚ) (j k : ℕ) :
    (-1:ℚ)^j * w / ((j:ℚ)+1)^k =
      (((-1:ℤ)^j*w.num:ℤ):ℚ) / ((w.den*(j+1)^k:ℕ):ℚ) := by
  push_cast
  calc
    _ = (-1:ℚ)^j * ((w.num:ℚ)/w.den) / ((j:ℚ)+1)^k := by rw [Rat.num_div_den]
    _ = _ := by ring

theorem intEtaTermLower_eq (w : ℚ) (j k B : ℕ) :
    (intEtaTermLower w j k B : ℚ) / B =
      ratRoundLower ((-1:ℚ)^j*w/((j:ℚ)+1)^k) B := by
  rw [ratEtaTerm_num_den, ratRoundLower_intDiv]
  rfl

theorem intEtaTermUpper_eq (w : ℚ) (j k B : ℕ) :
    (intEtaTermUpper w j k B : ℚ) / B =
      ratRoundUpper ((-1:ℚ)^j*w/((j:ℚ)+1)^k) B := by
  rw [ratEtaTerm_num_den, ratRoundUpper_intDiv]
  rfl

def ratEtaIntegerFastLower (M k B : ℕ) : ℚ :=
  (((ratEtaWeightTable M).mapIdx (fun j w => intEtaTermLower w j k B)).sum : ℤ) / B

def ratEtaIntegerFastUpper (M k B : ℕ) : ℚ :=
  (((ratEtaWeightTable M).mapIdx (fun j w => intEtaTermUpper w j k B)).sum : ℤ) / B

theorem intList_sum_div (xs : List ℤ) (B : ℕ) :
    ((xs.sum:ℤ):ℚ)/B = (xs.map (fun a : ℤ => (a:ℚ)/B)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.sum_cons, Int.cast_add, add_div, List.map_cons, ih]

theorem ratEtaIntegerFastLower_eq (M k B : ℕ) :
    ratEtaIntegerFastLower M k B = ratEtaIntegerRoundedLower M k B := by
  rw [←ratEtaIntegerTableLower_eq]
  unfold ratEtaIntegerFastLower ratEtaIntegerTableLower
  have he : (((ratEtaWeightTable M).mapIdx (fun j w => intEtaTermLower w j k B)).map
      (fun a : ℤ => (a:ℚ)/B)) =
      (ratEtaWeightTable M).mapIdx (fun j w =>
        ratRoundLower ((-1:ℚ)^j*w/((j:ℚ)+1)^k) B) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'; simp [intEtaTermLower_eq]
  rw [←he]
  exact intList_sum_div _ B

theorem ratEtaIntegerFastUpper_eq (M k B : ℕ) :
    ratEtaIntegerFastUpper M k B = ratEtaIntegerRoundedUpper M k B := by
  rw [←ratEtaIntegerTableUpper_eq]
  unfold ratEtaIntegerFastUpper ratEtaIntegerTableUpper
  have he : (((ratEtaWeightTable M).mapIdx (fun j w => intEtaTermUpper w j k B)).map
      (fun a : ℤ => (a:ℚ)/B)) =
      (ratEtaWeightTable M).mapIdx (fun j w =>
        ratRoundUpper ((-1:ℚ)^j*w/((j:ℚ)+1)^k) B) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'; simp [intEtaTermUpper_eq]
  rw [←he]
  exact intList_sum_div _ B

end ReciprocalXi


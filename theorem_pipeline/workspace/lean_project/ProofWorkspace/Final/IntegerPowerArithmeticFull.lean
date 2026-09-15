import ProofWorkspace.Final.IntegerEtaArithmeticFull
import ProofWorkspace.Final.RoundedExpBoundsFull
import ProofWorkspace.Final.RoundedSeriesScansFull
set_option autoImplicit false
namespace ReciprocalXi

theorem ratRoundLower_scaled_product (a c : ℤ) (B : ℕ) (hB : 0 < B) :
    ratRoundLower (((a:ℚ)/B)*((c:ℚ)/B)) B = (((a*c/(B:ℤ):ℤ):ℚ)/B) := by
  have hb : (B:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have he : (B:ℚ)*(((a:ℚ)/B)*((c:ℚ)/B)) = ((a*c:ℤ):ℚ)/B := by
    push_cast
    field_simp
  unfold ratRoundLower
  rw [he, Int.floor_div_natCast, Int.floor_intCast]

theorem ratRoundUpper_scaled_product (a c : ℤ) (B : ℕ) (hB : 0 < B) :
    ratRoundUpper (((a:ℚ)/B)*((c:ℚ)/B)) B = (((-(-(a*c)/(B:ℤ)):ℤ):ℚ)/B) := by
  have hb : (B:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have he : (B:ℚ)*(((a:ℚ)/B)*((c:ℚ)/B)) = -(((-(a*c):ℤ):ℚ)/B) := by
    push_cast
    field_simp
  unfold ratRoundUpper
  rw [he, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast, Int.cast_neg]

def intPowRoundLower (a : ℤ) (B : ℕ) : ℕ → ℤ
  | 0 => B
  | n+1 => intPowRoundLower a B n * a / (B:ℤ)

def intPowRoundUpper (a : ℤ) (B : ℕ) : ℕ → ℤ
  | 0 => B
  | n+1 => -(-(intPowRoundUpper a B n * a) / (B:ℤ))

theorem intPowRoundLower_eq (a : ℤ) (B n : ℕ) (hB : 0 < B) :
    ((intPowRoundLower a B n : ℤ):ℚ)/B = ratPowRoundLower ((a:ℚ)/B) B n := by
  induction n with
  | zero => simp [intPowRoundLower, ratPowRoundLower, ne_of_gt hB]
  | succ n ih =>
    rw [ratPowRoundLower, ←ih, ratRoundLower_scaled_product _ _ _ hB]
    rfl

theorem intPowRoundUpper_eq (a : ℤ) (B n : ℕ) (hB : 0 < B) :
    ((intPowRoundUpper a B n : ℤ):ℚ)/B = ratPowRoundUpper ((a:ℚ)/B) B n := by
  induction n with
  | zero => simp [intPowRoundUpper, ratPowRoundUpper, ne_of_gt hB]
  | succ n ih =>
    rw [ratPowRoundUpper, ←ih, ratRoundUpper_scaled_product _ _ _ hB]
    rfl
def ratExpScanIntegerLower (q : ℚ) (m n B : ℕ) : ℚ :=
  let a := Int.floor ((B:ℚ) * max 0 ((ratExpTaylorScan (q/m) n B).1 - ratExpUniformError n))
  (intPowRoundLower a B m:ℚ)/B

def ratExpScanIntegerUpper (q : ℚ) (m n B : ℕ) : ℚ :=
  let a := Int.ceil ((B:ℚ) * ((ratExpTaylorScan (q/m) n B).2 + ratExpUniformError n))
  (intPowRoundUpper a B m:ℚ)/B

theorem ratExpScanIntegerLower_eq (q : ℚ) (m n B : ℕ) (hB : 0 < B) :
    ratExpScanIntegerLower q m n B = ratExpFullyRoundedLower q m n B := by
  unfold ratExpScanIntegerLower
  rw [intPowRoundLower_eq _ _ _ hB, ratExpTaylorScan_lower]
  rfl

theorem ratExpScanIntegerUpper_eq (q : ℚ) (m n B : ℕ) (hB : 0 < B) :
    ratExpScanIntegerUpper q m n B = ratExpFullyRoundedUpper q m n B := by
  unfold ratExpScanIntegerUpper
  rw [intPowRoundUpper_eq _ _ _ hB, ratExpTaylorScan_upper]
  rfl

end ReciprocalXi


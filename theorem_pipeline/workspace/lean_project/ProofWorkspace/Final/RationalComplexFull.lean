import ProofWorkspace.Final.RoundedSeriesScansFull
import ProofWorkspace.Final.ComplexExpCertificatesFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def ratComplexValue (q : ℚ × ℚ) : ℂ := (q.1:ℂ)+(q.2:ℂ)*Complex.I

def ratComplexMul (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)

def ratComplexDivNat (a : ℚ × ℚ) (n : ℕ) : ℚ × ℚ := (a.1/n,a.2/n)

theorem ratComplexValue_re (q : ℚ × ℚ) : (ratComplexValue q).re=(q.1:ℝ) := by
  simp [ratComplexValue]

theorem ratComplexValue_im (q : ℚ × ℚ) : (ratComplexValue q).im=(q.2:ℝ) := by
  simp [ratComplexValue]

theorem ratComplexValue_add (a b : ℚ × ℚ) :
    ratComplexValue (a+b)=ratComplexValue a+ratComplexValue b := by
  unfold ratComplexValue
  simp only [Prod.fst_add, Prod.snd_add, Rat.cast_add]
  ring

theorem ratComplexValue_mul (a b : ℚ × ℚ) :
    ratComplexValue (ratComplexMul a b)=ratComplexValue a*ratComplexValue b := by
  apply Complex.ext <;>
    simp [ratComplexValue_re, ratComplexValue_im, ratComplexMul,
      Complex.mul_re, Complex.mul_im] <;> push_cast <;> ring

theorem ratComplexValue_divNat (a : ℚ × ℚ) (n : ℕ) :
    ratComplexValue (ratComplexDivNat a n)=ratComplexValue a/(n:ℂ) := by
  unfold ratComplexValue ratComplexDivNat
  push_cast
  ring

theorem ratComplexValue_norm_le (q : ℚ × ℚ) :
    ‖ratComplexValue q‖≤((|q.1|+|q.2|:ℚ):ℝ) := by
  simpa only [ratComplexValue_re, ratComplexValue_im, Rat.cast_add, Rat.cast_abs] using
    Complex.norm_le_abs_re_add_abs_im (ratComplexValue q)

theorem ratComplexValue_norm_le_one (q : ℚ × ℚ) (hq : q.1^2+q.2^2≤1) :
    ‖ratComplexValue q‖≤1 := by
  have he : ‖ratComplexValue q‖^2=(q.1:ℝ)^2+(q.2:ℝ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ratComplexValue_re, ratComplexValue_im]
    ring
  have hq' : (q.1:ℝ)^2+(q.2:ℝ)^2≤1 := by exact_mod_cast hq
  nlinarith [norm_nonneg (ratComplexValue q)]

def ratComplexExpTerm (q : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | n+1 => ratComplexDivNat (ratComplexMul (ratComplexExpTerm q n) q) (n+1)

theorem ratComplexExpTerm_value (q : ℚ × ℚ) (n : ℕ) :
    ratComplexValue (ratComplexExpTerm q n)=(ratComplexValue q)^n/(n.factorial:ℂ) := by
  induction n with
  | zero => simp [ratComplexExpTerm, ratComplexValue]
  | succ n ih =>
    rw [ratComplexExpTerm, ratComplexValue_divNat, ratComplexValue_mul, ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring

def ratComplexExpTaylorScan (q : ℚ × ℚ) (N : ℕ) : ℚ × ℚ :=
  ratPairSumLoop (fun j p ↦ ratComplexDivNat (ratComplexMul p q) (j+1)) N 0 (1,0) (0,0)

theorem ratComplexExpTaylorScan_value (q : ℚ × ℚ) (N : ℕ) :
    ratComplexValue (ratComplexExpTaylorScan q N)=
      ∑ n ∈ Finset.range N, (ratComplexValue q)^n/(n.factorial:ℂ) := by
  have he := ratPairSumLoop_eq
    (fun j p ↦ ratComplexDivNat (ratComplexMul p q) (j+1))
    (ratComplexExpTerm q) (fun j ↦ rfl) N 0 (0,0)
  have hzero : ((0,0):ℚ × ℚ)=0 := rfl
  simp only [ratComplexExpTerm, Nat.zero_add, hzero, zero_add] at he
  unfold ratComplexExpTaylorScan
  rw [hzero, he]
  rw [← Finset.sum_congr rfl (fun n hn ↦ ratComplexExpTerm_value q n)]
  clear he
  induction N with
  | zero => simp [ratComplexValue]
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ratComplexValue_add, ih]

end ReciprocalXi

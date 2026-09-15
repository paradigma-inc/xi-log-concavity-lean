import ProofWorkspace.Final.XiProductIdentityFull
import ProofWorkspace.Final.XiZeroBudgetFull
import ProofWorkspace.Final.XiFourierRealFull
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
open Complex
namespace ReciprocalXi

def F_pairMoment (m : ℕ) : ℝ :=
  ∑' z : FPositiveZeroOccurrence, (((F_pairRoot z)⁻¹)^(2*m)).re

def F_momentLog (u : ℝ) : ℝ := -Real.log ((reciprocalTransform u).re)

def F_momentTaylor (N : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N+1), (-1:ℝ)^(m+1)*u^(2*m)/(m:ℝ)*F_pairMoment m

theorem norm_F_pairRoot_inverse_power_le (z : FPositiveZeroOccurrence)
    (m : ℕ) (hm : 0<m) :
    ‖((F_pairRoot z)⁻¹)^(2*m)‖≤(‖F_pairRoot z‖^2)⁻¹ := by
  have hr := F_zero_norm_gt_one _ (F_pairRoot_is_zero z)
  have hsq : (1:ℝ)≤‖F_pairRoot z‖^2 := by nlinarith
  have hi : (‖F_pairRoot z‖^2)⁻¹≤1 := inv_le_one_of_one_le₀ hsq
  have he : ‖((F_pairRoot z)⁻¹)^(2*m)‖=((‖F_pairRoot z‖^2)⁻¹)^m := by
    rw [norm_pow,norm_inv,pow_mul,inv_pow]
  rw [he]
  exact pow_le_of_le_one (by positivity) hi (by omega)

theorem summable_F_pairRoot_inverse_power (m : ℕ) (hm : 0<m) :
    Summable (fun z : FPositiveZeroOccurrence ↦ ((F_pairRoot z)⁻¹)^(2*m)) :=
  summable_F_pairRoot_inv_norm_sq.of_norm_bounded
    (fun z ↦ norm_F_pairRoot_inverse_power_le z m hm)

theorem summable_F_pairMoment_terms (m : ℕ) (hm : 0<m) :
    Summable (fun z : FPositiveZeroOccurrence ↦ (((F_pairRoot z)⁻¹)^(2*m)).re) :=
  (Complex.hasSum_re (summable_F_pairRoot_inverse_power m hm).hasSum).summable

theorem F_pairTerm_imaginary (z : FPositiveZeroOccurrence) (u : ℝ) :
    F_pairTerm z (I*(u:ℂ))=(u:ℂ)^2/(F_pairRoot z)^2 := by
  rw [F_pairTerm,mul_div_assoc,mul_pow,Complex.I_sq]
  ring

theorem F_pairFactor_imaginary_ne_zero (z : FPositiveZeroOccurrence) (u : ℝ) :
    1+F_pairTerm z (I*(u:ℂ))≠0 := by
  intro hz
  rcases (F_pairFactor_zero_iff z (I*(u:ℂ))).mp hz with he | he
  · exact F_imaginary_axis_ne_zero u (he ▸ F_pairRoot_is_zero z)
  · have hf := F_imaginary_axis_ne_zero u
    rw [he,F_even] at hf
    exact hf (F_pairRoot_is_zero z)

theorem summable_F_pair_logarithm (u : ℝ) :
    Summable (fun z : FPositiveZeroOccurrence ↦ Complex.log (1+F_pairTerm z (I*(u:ℂ)))) :=
  Complex.summable_log_one_add_of_summable (summable_norm_F_pairTerm (I*(u:ℂ))).of_norm

theorem F_momentLog_eq_sum_logarithm (u : ℝ) :
    F_momentLog u=
      (∑' z : FPositiveZeroOccurrence, Complex.log (1+F_pairTerm z (I*(u:ℂ)))).re := by
  have he := Complex.cexp_tsum_eq_tprod
    (fun z ↦ F_pairFactor_imaginary_ne_zero z u) (summable_F_pair_logarithm u)
  have hp :
      Complex.exp (∑' z : FPositiveZeroOccurrence, Complex.log (1+F_pairTerm z (I*(u:ℂ))))=
        (reciprocalTransform u)⁻¹ := by
    rw [he]
    change F_pairedProduct (I*(u:ℂ))=(F 0/F (I*(u:ℂ)))⁻¹
    rw [←F_div_zero_eq_pairedProduct,inv_div]
  have hq : ‖reciprocalTransform u‖=(reciprocalTransform u).re := by
    have hreal := Complex.conj_eq_iff_re.mp (reciprocalTransform_conj u)
    calc
      _=‖((reciprocalTransform u).re:ℂ)‖ := congrArg norm hreal.symm
      _=_ := by rw [Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (reciprocalTransform_re_pos u)]
  have hh := congrArg (fun w : ℂ ↦ Real.log ‖w‖) hp
  dsimp only at hh
  rw [Complex.norm_exp,Real.log_exp,norm_inv,hq,Real.log_inv] at hh
  exact hh.symm

theorem F_pairTerm_small_norm (z : FPositiveZeroOccurrence) (u d : ℝ)
    (hd : 0<d) (hroot : d≤(F_pairRoot z).re) :
    ‖F_pairTerm z (I*(u:ℂ))‖≤u^2/d^2 := by
  have hr : d≤‖F_pairRoot z‖ := hroot.trans (Complex.re_le_norm _)
  rw [norm_F_pairTerm,norm_mul,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (pow_le_pow_left₀ hd.le hr 2)

theorem F_pair_logTaylor_term_error (z : FPositiveZeroOccurrence) (N : ℕ)
    (u d : ℝ) (hd : 0<d) (hroot : d≤(F_pairRoot z).re) (hu : u^2<d^2) :
    ‖Complex.log (1+F_pairTerm z (I*(u:ℂ)))-
        Complex.logTaylor (N+1) (F_pairTerm z (I*(u:ℂ)))‖≤
      (u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2)))*(‖F_pairRoot z‖^2)⁻¹ := by
  let t := F_pairTerm z (I*(u:ℂ))
  have hR : u^2/d^2<1 := (div_lt_one (by positivity)).mpr hu
  have ht : ‖t‖≤u^2/d^2 := F_pairTerm_small_norm z u d hd hroot
  have hden : 0 < 1-‖t‖ := by linarith
  have hdenR : 0 < 1-u^2/d^2 := by linarith
  have he := Complex.norm_log_sub_logTaylor_le N (ht.trans_lt hR)
  have hp : ‖t‖^N≤(u^2/d^2)^N := pow_le_pow_left₀ (norm_nonneg _) ht N
  have hi : (1-‖t‖)⁻¹≤(1-u^2/d^2)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have ht' : ‖t‖=u^2*(‖F_pairRoot z‖^2)⁻¹ := by
    rw [norm_F_pairTerm,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
  apply he.trans
  calc
    _≤(‖t‖*(u^2/d^2)^N)*(1-u^2/d^2)⁻¹/(N+1:ℕ) := by
      rw [pow_succ']
      push_cast
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hi
          (inv_nonneg.mpr hden.le)
          (mul_nonneg (norm_nonneg t)
            (pow_nonneg (div_nonneg (sq_nonneg u) (sq_nonneg d)) N)))
        (show 0 ≤ (N:ℝ)+1 by positivity)
    _=_ := by rw [ht']; push_cast; field_simp

theorem F_logTaylor_term_summable (m : ℕ) (u : ℝ) :
    Summable (fun z : FPositiveZeroOccurrence ↦
      (-1:ℂ)^(m+1)*(F_pairTerm z (I*(u:ℂ)))^m/(m:ℂ)) := by
  by_cases hm : m=0
  · subst m
    simp
  · have he (z : FPositiveZeroOccurrence) :
        (-1:ℂ)^(m+1)*(F_pairTerm z (I*(u:ℂ)))^m/(m:ℂ)=
          ((-1:ℂ)^(m+1)*(u:ℂ)^(2*m)/(m:ℂ))*((F_pairRoot z)⁻¹)^(2*m) := by
      rw [F_pairTerm_imaginary,div_pow,←pow_mul,←pow_mul,div_eq_mul_inv,inv_pow]
      ring
    simp_rw [he]
    exact (summable_F_pairRoot_inverse_power m (by omega)).mul_left _

theorem summable_F_logTaylor (N : ℕ) (u : ℝ) :
    Summable (fun z : FPositiveZeroOccurrence ↦
      Complex.logTaylor (N+1) (F_pairTerm z (I*(u:ℂ)))) := by
  unfold Complex.logTaylor
  exact summable_sum (fun m _ ↦ F_logTaylor_term_summable m u)

theorem F_logTaylor_sum_error (N : ℕ) (u d : ℝ) (hd : 0<d)
    (hroot : ∀ z : FPositiveZeroOccurrence, d≤(F_pairRoot z).re) (hu : u^2<d^2) :
    |F_momentLog u-
      (∑' z : FPositiveZeroOccurrence,
        Complex.logTaylor (N+1) (F_pairTerm z (I*(u:ℂ)))).re|≤
      (u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2)))*
        (∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹) := by
  have hh := tsum_of_norm_bounded
    (summable_F_pairRoot_inv_norm_sq.hasSum.mul_left
      (u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2))))
    (fun z ↦ F_pair_logTaylor_term_error z N u d hd (hroot z) hu)
  rw [(summable_F_pair_logarithm u).tsum_sub (summable_F_logTaylor N u)] at hh
  rw [F_momentLog_eq_sum_logarithm]
  exact (Complex.abs_re_le_norm _).trans hh

theorem F_logTaylor_term_re (z : FPositiveZeroOccurrence) (m : ℕ) (u : ℝ) :
    ((-1:ℂ)^(m+1)*(F_pairTerm z (I*(u:ℂ)))^m/(m:ℂ)).re=
      ((-1:ℝ)^(m+1)*u^(2*m)/(m:ℝ))*(((F_pairRoot z)⁻¹)^(2*m)).re := by
  have he : (-1:ℂ)^(m+1)*(F_pairTerm z (I*(u:ℂ)))^m/(m:ℂ)=
      ((((-1:ℝ)^(m+1)*u^(2*m)/(m:ℝ)):ℝ):ℂ)*((F_pairRoot z)⁻¹)^(2*m) := by
    rw [F_pairTerm_imaginary,div_pow,←pow_mul,←pow_mul]
    push_cast
    rw [div_eq_mul_inv,inv_pow]
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem F_logTaylor_sum_eq_momentTaylor (N : ℕ) (u : ℝ) :
    (∑' z : FPositiveZeroOccurrence,
      Complex.logTaylor (N+1) (F_pairTerm z (I*(u:ℂ)))).re=F_momentTaylor N u := by
  rw [Complex.re_tsum (summable_F_logTaylor N u)]
  simp_rw [Complex.logTaylor,Complex.re_sum,F_logTaylor_term_re]
  have hs (m : ℕ) : Summable (fun z : FPositiveZeroOccurrence ↦
      ((-1:ℝ)^(m+1)*u^(2*m)/(m:ℝ))*(((F_pairRoot z)⁻¹)^(2*m)).re) := by
    have hh := (Complex.hasSum_re (F_logTaylor_term_summable m u).hasSum).summable
    simpa only [F_logTaylor_term_re] using hh
  rw [Summable.tsum_finsetSum (fun m _ ↦ hs m)]
  simp only [tsum_mul_left,F_momentTaylor,F_pairMoment]

theorem F_momentTaylor_actual_error (N : ℕ) (u d : ℝ) (hd : 0<d)
    (hroot : ∀ z : FPositiveZeroOccurrence, d≤(F_pairRoot z).re) (hu : u^2<d^2) :
    |F_momentLog u-F_momentTaylor N u|≤
      (u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2)))*
        (∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹) := by
  have he := F_logTaylor_sum_error N u d hd hroot hu
  rw [F_logTaylor_sum_eq_momentTaylor] at he
  exact he

theorem F_momentTaylor_error_of_mass_bound (N : ℕ) (u d C : ℝ) (hd : 0<d)
    (hroot : ∀ z : FPositiveZeroOccurrence, d≤(F_pairRoot z).re) (hu : u^2<d^2)
    (hC : (∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹)≤C) :
    |F_momentLog u-F_momentTaylor N u|≤
      C*u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2)) := by
  have hR : u^2/d^2<1 := (div_lt_one (by positivity)).mpr hu
  have hdenR : 0 < 1-u^2/d^2 := by linarith
  apply (F_momentTaylor_actual_error N u d hd hroot hu).trans
  calc
    _≤(u^2*(u^2/d^2)^N/((N+1:ℕ)*(1-u^2/d^2)))*C :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _=_ := by ring

end ReciprocalXi

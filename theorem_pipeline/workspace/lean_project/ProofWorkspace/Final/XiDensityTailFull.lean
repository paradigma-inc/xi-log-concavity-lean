import ProofWorkspace.Final.XiDensityConvolutionFull
import ProofWorkspace.Final.DensityConditionalFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
namespace ReciprocalXi

variable (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ} (ha : 0<a) (hab : a<b)
  (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
  (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace
    ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) t).re)

include ha hab hz₁ hz₂ hpos

theorem density_iterated_deriv_eq_twoLaplace (j : ℕ) (hj : j≤2) :
    deriv^[j] density = laplaceConvolutionJet (F_selectedResidualLaw
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ))
        (a*b/(2*(b^2-a^2))) a b j := by
  classical
  let S : Set FPositiveZeroOccurrence :=
    ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
  letI := F_selectedResidualLaw_isProbability S hpos
  have hd := funext (density_eq_twoLaplace_convolution z₁ z₂ ha hab hz₁ hz₂
    (F_pairConj_compl_two_real z₁ z₂ hz₁ hz₂) hpos)
  rw [hd]
  apply laplaceConvolution_iterated_deriv_eq _ _ _ _ 0 j hj
    (by apply le_of_lt; exact div_pos (mul_pos ha (ha.trans hab)) (by nlinarith))
    ha.le (ha.trans hab).le le_rfl
  simpa only [zero_mul, Real.exp_zero] using
    (integrable_const (1:ℝ) (μ:=F_selectedResidualLaw S))

theorem density_twoLaplace_derivative_remainder
    {R L M : ℝ} (hbR : b≤R) (hRL : R<L)
    (hgap : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      L^2<((F_pairRoot z)^2).re)
    (hF : F (R:ℂ)≠0)
    (hM : 2*(F 0*(∏ z∈({z₁,z₂}:Finset FPositiveZeroOccurrence),
      (1-(R:ℂ)^2/(F_pairRoot z)^2))/F (R:ℂ)).re≤M)
    (x : ℝ) (hx : 0≤x) (j : ℕ) (hj : j≤2) :
    let μ := F_selectedResidualLaw
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
    let C := a*b/(2*(b^2-a^2))
    |(deriv^[j] density) x - (-1:ℝ)^j*C*
      (b*a^j*Real.exp (-a*x)*exponentialMoment μ a -
        a*b^j*Real.exp (-b*x)*exponentialMoment μ b)| ≤
      (2*C*M*(b*a^j+a*b^j))*Real.exp (-R*x) := by
  classical
  dsimp only
  have hR : 0<R := (ha.trans hab).trans_le hbR
  have hm := F_selectedResidualLaw_absoluteMoment_quotient ({z₁,z₂}:Finset FPositiveZeroOccurrence)
    (F_pairConj_compl_two_real z₁ z₂ hz₁ hz₂) hpos (hR.trans hRL) hgap
    (by simpa only [abs_of_pos hR] using hRL) hF
  rw [density_iterated_deriv_eq_twoLaplace z₁ z₂ ha hab hz₁ hz₂ hpos j hj]
  apply laplaceConvolutionJet_remainder_to_moments _ _ _ _ R M x j
    (by apply le_of_lt; exact div_pos (mul_pos ha (ha.trans hab)) (by nlinarith))
    ha.le (ha.trans hab).le (hab.le.trans hbR) hbR hx hm.1 (hm.2.trans hM)

theorem density_tail_enclosures_nonempty
    {R L M : ℝ} (hbR : b<R) (hRL : R<L) (hMpos : 0<M)
    (hgap : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      L^2<((F_pairRoot z)^2).re)
    (hF : F (R:ℂ)≠0)
    (hM : 2*(F 0*(∏ z∈({z₁,z₂}:Finset FPositiveZeroOccurrence),
      (1-(R:ℂ)^2/(F_pairRoot z)^2))/F (R:ℂ)).re≤M)
    (hOverlap :
      let C := a*b/(2*(b^2-a^2))
      let D := fun j : ℕ ↦ 2*C*M*(b*a^j+a*b^j)
      tailThreshold a b R (tailU1 C a b (D 0) (D 1) (D 2))
        (tailU2 C a b (D 0) (D 1) (D 2))
        (tailU3 C a b (D 0) (D 1) (D 2))≤318/100) :
    Nonempty DensityTailEnclosures := by
  classical
  let S : Set FPositiveZeroOccurrence :=
    ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
  let μ := F_selectedResidualLaw S
  let C := a*b/(2*(b^2-a^2))
  let D := fun j : ℕ ↦ 2*C*M*(b*a^j+a*b^j)
  let A := C*b*exponentialMoment μ a
  let B := C*a*exponentialMoment μ b
  have hC : 0<C := div_pos (mul_pos ha (ha.trans hab)) (by nlinarith)
  have hb : 0<b := ha.trans hab
  have hR : 0<R := (ha.trans hab).trans hbR
  letI := F_selectedResidualLaw_isProbability S hpos
  have hm := F_selectedResidualLaw_absoluteMoment_quotient ({z₁,z₂}:Finset FPositiveZeroOccurrence)
    (F_pairConj_compl_two_real z₁ z₂ hz₁ hz₂) hpos (hR.trans hRL) hgap
    (by simpa only [abs_of_pos hR] using hRL) hF
  have hEven := F_selectedResidualLaw_even S hpos
  have hma := exponentialMoment_one_le_of_even μ a R ha.le (hab.le.trans hbR.le) hEven hm.1
  have hmb := exponentialMoment_one_le_of_even μ b R (ha.trans hab).le hbR.le hEven hm.1
  have hA : C*b≤A := by
    dsimp [A]
    nlinarith [mul_pos hC (ha.trans hab)]
  have hB : C*a≤B := by
    dsimp [B]
    nlinarith [mul_pos hC ha]
  refine ⟨{
    A := A, B := B, C := C, a := a, b := b, R := R
    D0 := D 0, D1 := D 1, D2 := D 2
    C_pos := hC, a_pos := ha, a_lt_b := hab, b_lt_R := hbR
    A_lower := hA, B_lower := hB
    D0_pos := ?_, D1_nonneg := ?_, D2_pos := ?_
    overlap := hOverlap
    derivative_errors := ?_ }⟩
  · change 0<2*C*M*(b*a^0+a*b^0); positivity
  · change 0≤2*C*M*(b*a^1+a*b^1); positivity
  · change 0<2*C*M*(b*a^2+a*b^2); positivity
  · intro x hx
    have hx0 : 0≤x := (tailThreshold_nonneg _ _ _ _ _ _).trans hx
    have he (j : ℕ) (hj : j≤2) := density_twoLaplace_derivative_remainder
      z₁ z₂ ha hab hz₁ hz₂ hpos hbR.le hRL hgap hF hM x hx0 j hj
    have h0 := he 0 (by omega)
    have h1 := he 1 (by omega)
    have h2 := he 2 (by omega)
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, mul_one] at h0
    simp only [Function.iterate_one, pow_one] at h1
    simp only [Function.iterate_succ_apply', Function.iterate_one] at h2
    constructor
    · convert h0 using 1 <;> dsimp [A, B, C, D, μ, S] <;> congr 1 <;> ring
    constructor
    · convert h1 using 1 <;> dsimp [A, B, C, D, μ, S] <;> congr 1 <;> ring
    · convert h2 using 1 <;> dsimp [A, B, C, D, μ, S] <;> congr 1 <;> ring

end ReciprocalXi

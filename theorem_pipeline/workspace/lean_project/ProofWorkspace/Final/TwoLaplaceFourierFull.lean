import ProofWorkspace.Final.LaplaceAtomFourierFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem twoLaplace_character_split (C a b u x : ℝ) :
    (twoLaplaceJet C a b 0 x:ℂ)*Complex.exp ((u:ℂ)*(x:ℂ)*I)=
      (C:ℂ)*((b:ℂ)*laplaceAtomCharacter a u x-(a:ℂ)*laplaceAtomCharacter b u x) := by
  rw [twoLaplaceJet_zero]
  simp only [laplaceAtomCharacter, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

theorem integrable_twoLaplace_character (C : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b) (u : ℝ) :
    Integrable (fun x : ℝ ↦ (twoLaplaceJet C a b 0 x:ℂ)*Complex.exp ((u:ℂ)*(x:ℂ)*I)) := by
  exact (((integrable_laplaceAtomCharacter ha u).const_mul (b:ℂ)).sub
    ((integrable_laplaceAtomCharacter hb u).const_mul (a:ℂ))).const_mul (C:ℂ) |>.congr
      (Eventually.of_forall (fun x ↦ (twoLaplace_character_split C a b u x).symm))

theorem integral_twoLaplace_character (C : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b) (u : ℝ) :
    (∫ x : ℝ, (twoLaplaceJet C a b 0 x:ℂ)*Complex.exp ((u:ℂ)*(x:ℂ)*I))=
      (C:ℂ)*((b:ℂ)*(2*(a:ℂ)/((a:ℂ)^2+(u:ℂ)^2))-
        (a:ℂ)*(2*(b:ℂ)/((b:ℂ)^2+(u:ℂ)^2))) := by
  simp_rw [twoLaplace_character_split]
  rw [integral_const_mul, integral_sub
    ((integrable_laplaceAtomCharacter ha u).const_mul (b:ℂ))
    ((integrable_laplaceAtomCharacter hb u).const_mul (a:ℂ)),
    integral_const_mul, integral_const_mul, integral_laplaceAtomCharacter ha,
    integral_laplaceAtomCharacter hb]

theorem integral_twoLaplace_normalized_character {a b : ℝ} (ha : 0<a) (hab : a<b) (u : ℝ) :
    (∫ x : ℝ, (twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x:ℂ)*
      Complex.exp ((u:ℂ)*(x:ℂ)*I))=
      ((a:ℂ)^2/((a:ℂ)^2+(u:ℂ)^2))*((b:ℂ)^2/((b:ℂ)^2+(u:ℂ)^2)) := by
  rw [integral_twoLaplace_character _ ha (ha.trans hab)]
  have had : (a:ℂ)^2+(u:ℂ)^2≠0 := by
    exact_mod_cast (show (a^2+u^2:ℝ)≠0 by nlinarith [sq_nonneg u])
  have hbd : (b:ℂ)^2+(u:ℂ)^2≠0 := by
    exact_mod_cast (show (b^2+u^2:ℝ)≠0 by nlinarith [sq_nonneg u])
  have hab' : (b:ℂ)^2-(a:ℂ)^2≠0 := by
    exact_mod_cast (show (b^2-a^2:ℝ)≠0 by nlinarith)
  push_cast
  field_simp
  ring

theorem integrable_twoLaplace_kernel (C : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Integrable (twoLaplaceJet C a b 0) := by
  have hh := Complex.reCLM.integrable_comp (integrable_twoLaplace_character C ha hb 0)
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Complex.reCLM_apply, Complex.ofReal_re] using hh

end ReciprocalXi

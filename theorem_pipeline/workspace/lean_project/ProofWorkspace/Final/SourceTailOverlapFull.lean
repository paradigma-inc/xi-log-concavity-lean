import ProofWorkspace.Final.TailBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem twoLaplace_tail_coefficients_simplified (C a b M : ℝ)
    (hC : C≠0) (ha : 0<a) (hab : a<b) :
    let D := fun j : ℕ ↦ 2*C*M*(b*a^j+a*b^j)
    tailU1 C a b (D 0) (D 1) (D 2)=2*M*(a^2+6*a*b+b^2)/(b-a)^2 ∧
    tailU2 C a b (D 0) (D 1) (D 2)=2*M*(a^2+6*a*b+b^2)/(b-a)^2 ∧
    tailU3 C a b (D 0) (D 1) (D 2)=4*M^2*(a^2+6*a*b+b^2)/(b-a)^2 := by
  have ha0 := ha.ne'
  have hb0 := (ha.trans hab).ne'
  have hd0 : b-a≠0 := sub_ne_zero.mpr hab.ne'
  dsimp [tailU1, tailU2, tailU3]
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

theorem exp_1893_div100_lower : (165000000:ℝ)≤Real.exp (1893/100) := by
  have h := (ratExp_scaled_enclosure (1893/100) 20 12
    (by norm_num) (by norm_num) (by norm_num)).1
  have hc : (165000000:ℚ)≤ratExpScaledLower (1893/100) 20 12 := by
    norm_num [ratExpScaledLower, ratExpTaylor, ratExpError, Finset.sum_range_succ, Nat.factorial]
  have hc' : (165000000:ℝ)≤(ratExpScaledLower (1893/100) 20 12:ℝ) := by exact_mod_cast hc
  exact hc'.trans (by simpa using h)

theorem source_tail_ratio_upper {a b : ℝ}
    (ha0 : 28269/1000≤a) (ha1 : a≤28270/1000)
    (hb0 : 42044/1000≤b) (hb1 : b≤42045/1000) :
    2*268341*(a^2+6*a*b+b^2)/(b-a)^2≤27500000 := by
  have ha : 0≤a := by linarith
  have hb : 0≤b := by linarith
  have hnum : a^2+6*a*b+b^2≤
      (28270/1000:ℝ)^2+6*(28270/1000)*(42045/1000)+(42045/1000)^2 := by
    gcongr
  have hd : 13774/1000≤b-a := by linarith
  have hden : (13774/1000:ℝ)^2≤(b-a)^2 := by nlinarith
  have hdpos : 0<(b-a)^2 := by nlinarith
  apply (div_le_iff₀ hdpos).mpr
  nlinarith

theorem source_tail_threshold_le_overlap {a b : ℝ}
    (ha0 : 28269/1000≤a) (ha1 : a≤28270/1000)
    (hb0 : 42044/1000≤b) (hb1 : b≤42045/1000) :
    let C := a*b/(2*(b^2-a^2))
    let D := fun j : ℕ ↦ 2*C*268341*(b*a^j+a*b^j)
    tailThreshold a b 48 (tailU1 C a b (D 0) (D 1) (D 2))
      (tailU2 C a b (D 0) (D 1) (D 2))
      (tailU3 C a b (D 0) (D 1) (D 2))≤318/100 := by
  have ha : 0<a := by linarith
  have hb : 0<b := by linarith
  have hab : a<b := by linarith
  have hC : 0<a*b/(2*(b^2-a^2)) := div_pos (mul_pos ha hb) (by nlinarith)
  dsimp only
  obtain ⟨h1,h2,h3⟩ := twoLaplace_tail_coefficients_simplified
    (a*b/(2*(b^2-a^2))) a b 268341 hC.ne' ha hab
  dsimp only at h1 h2 h3
  rw [h1,h2,h3]
  let U := 2*268341*(a^2+6*a*b+b^2)/(b-a)^2
  have hu : U≤27500000 := source_tail_ratio_upper ha0 ha1 hb0 hb1
  have hupos : 0<U := by
    dsimp [U]
    apply div_pos (by positivity) (sq_pos_of_ne_zero (sub_ne_zero.mpr hab.ne'))
  have h3eq : 4*268341^2*(a^2+6*a*b+b^2)/(b-a)^2=2*268341*U := by
    dsimp [U]; ring
  rw [h3eq]
  change max 0 (max (Real.log (6*U)/(48-b))
    (max (Real.log (6*U)/(48-a)) (Real.log (6*(2*268341*U))/(2*48-a-b))))≤318/100
  have hlog (r x : ℝ) (hr : 0<r) (hx : 6*U≤Real.exp (r*x)) :
      Real.log (6*U)/r≤x := by
    apply (div_le_iff₀ hr).mpr
    have hh := (Real.log_le_iff_le_exp (by positivity : 0<6*U)).mpr hx
    nlinarith
  have he : 6*U≤Real.exp (1893/100) := by
    exact (by linarith : 6*U≤165000000).trans exp_1893_div100_lower
  apply max_le (by norm_num)
  apply max_le
  · apply hlog _ _ (by linarith)
    exact he.trans (Real.exp_le_exp.mpr (by nlinarith))
  apply max_le
  · apply hlog _ _ (by linarith)
    exact he.trans (Real.exp_le_exp.mpr (by nlinarith))
  · apply (div_le_iff₀ (by linarith : 0<2*48-a-b)).mpr
    have hexp : (165000000:ℝ)^2≤Real.exp (2*(1893/100)) := by
      rw [show 2*(1893/100:ℝ)=1893/100+1893/100 by ring, Real.exp_add, ← pow_two]
      exact pow_le_pow_left₀ (by norm_num) exp_1893_div100_lower 2
    have hu3 : 6*(2*268341*U)≤(165000000:ℝ)^2 := by nlinarith
    have hh := (Real.log_le_iff_le_exp (by positivity : 0<6*(2*268341*U))).mpr
      (hu3.trans (hexp.trans (Real.exp_le_exp.mpr (by nlinarith :
        2*(1893/100)≤(2*48-a-b)*(318/100)))))
    nlinarith

end ReciprocalXi

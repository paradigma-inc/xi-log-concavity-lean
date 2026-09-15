import ProofWorkspace.Final.XiLowZeroIntegralFull
import ProofWorkspace.Final.XiThetaPanelCoefficientErrorFull
import ProofWorkspace.Final.RationalThetaTransitionFull

set_option autoImplicit false
noncomputable section
open Complex
namespace ReciprocalXi

theorem lowZeroThetaTaylorCoefficient_scaled_atoms (x c h : ℝ) (n : ℕ) (hc : 0<c) :
    lowZeroThetaTaylorCoefficient x c n*(h:ℂ)^n=
      2*(∑ k ∈ Finset.range 5,
        scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
          (Real.pi*((k:ℝ)+1)^2) h n) := by
  have hz : (c:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc)
  have hd : ∀ k ∈ Finset.range 5, ContDiffAt ℂ n
      (complexPowerExpAtom (complexThetaExponent x) (Real.pi*((k:ℝ)+1)^2)) (c:ℂ) :=
    fun k hk ↦ (complexPowerExpAtom_analyticAt _ _ _ hz).contDiffAt
  unfold lowZeroThetaTaylorCoefficient
  rw [complexThetaFiniteIntegrand_atom_sum, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sum hd]
  unfold scaledPowerExpCoefficient complexPowerExpTaylorCoefficient
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem lowZeroThetaTaylorPanelValue_scaled (x c h : ℝ) (N : ℕ) :
    lowZeroThetaTaylorPanelValue x c h N=
      ∑ n ∈ Finset.range N, (h*(1-(-1:ℝ)^(n+1))/(n+1:ℕ))*
        (lowZeroThetaTaylorCoefficient x c n*(h:ℂ)^n).re := by
  unfold lowZeroThetaTaylorPanelValue
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_pow, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show (-h)^(n+1)=(-1:ℝ)^(n+1)*h^(n+1) by rw [← mul_pow]; congr 1; ring,
    pow_succ h n]
  ring

theorem lowZeroScaledIntegralWeight_abs_le_two (h : ℝ) (n : ℕ)
    (hh0 : 0≤h) (hh1 : h≤1) : |theta48ScaledIntegralWeight h n|≤2 := by
  have hw := theta48ScaledIntegralWeight_abs_le_one (h/2) n
    (by linarith) (by linarith)
  have he : theta48ScaledIntegralWeight h n=2*theta48ScaledIntegralWeight (h/2) n := by
    unfold theta48ScaledIntegralWeight
    ring
  rw [he,abs_mul]
  norm_num
  linarith

def lowZeroApproxPanelValue (h : ℝ) (w : ℕ → ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range 80, theta48ScaledIntegralWeight h n*
    (2*(∑ k ∈ Finset.range 5, (w k n).re))

theorem lowZeroPanel_coefficient_error (x c h epsilon : ℝ) (w : ℕ → ℕ → ℂ)
    (hc : 0<c) (hh0 : 0≤h) (hh1 : h≤1) (he : 0≤epsilon)
    (hw : ∀ k : ℕ, k<5 → ∀ n : ℕ, n<80 →
      ‖scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
        (Real.pi*((k:ℝ)+1)^2) h n-w k n‖≤epsilon) :
    |lowZeroThetaTaylorPanelValue x c h 80-lowZeroApproxPanelValue h w|≤1600*epsilon := by
  rw [lowZeroThetaTaylorPanelValue_scaled]
  unfold lowZeroApproxPanelValue
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range 80, |theta48ScaledIntegralWeight h n*
        (lowZeroThetaTaylorCoefficient x c n*(h:ℂ)^n).re-
        theta48ScaledIntegralWeight h n*(2*∑ k ∈ Finset.range 5, (w k n).re)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range 80, 20*epsilon := by
      apply Finset.sum_le_sum
      intro n hn
      have hn80 : n<80 := Finset.mem_range.mp hn
      rw [← mul_sub,abs_mul,lowZeroThetaTaylorCoefficient_scaled_atoms x c h n hc]
      have hRe : (2*∑ k ∈ Finset.range 5,
          scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
            (Real.pi*((k:ℝ)+1)^2) h n).re-
          2*∑ k ∈ Finset.range 5, (w k n).re=
          2*∑ k ∈ Finset.range 5,
            (scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
              (Real.pi*((k:ℝ)+1)^2) h n-w k n).re := by
        norm_num [Complex.mul_re,Complex.re_sum,Complex.sub_re,Finset.sum_sub_distrib]
        <;> ring
      rw [hRe,abs_mul]
      have hsum : |∑ k ∈ Finset.range 5,
          (scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
            (Real.pi*((k:ℝ)+1)^2) h n-w k n).re|≤5*epsilon := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        calc
          _ ≤ ∑ _k ∈ Finset.range 5, epsilon := by
            apply Finset.sum_le_sum
            intro k hk
            exact (Complex.abs_re_le_norm _).trans (hw k (Finset.mem_range.mp hk) n hn80)
          _ = _ := by simp
      have hweight := lowZeroScaledIntegralWeight_abs_le_two h n hh0 hh1
      have hprod := mul_le_mul hweight hsum (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      norm_num at hprod ⊢
      nlinarith
    _ = _ := by simp; ring

def ratLowZeroApproxPanelValue (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ) : ℚ :=
  ∑ n ∈ Finset.range 80, (h*(1-(-1:ℚ)^(n+1))/(n+1)) *
    (2*∑ k ∈ Finset.range 5, (w k n).1)

theorem ratLowZeroApproxPanelValue_cast (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ) :
    (ratLowZeroApproxPanelValue h w:ℝ)=
      lowZeroApproxPanelValue h (fun k n ↦ ratComplexValue (w k n)) := by
  unfold ratLowZeroApproxPanelValue lowZeroApproxPanelValue theta48ScaledIntegralWeight
  simp only [ratComplexValue_re]
  push_cast
  rfl

theorem ratLowZeroPanel_error (x c : ℝ) (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ)
    (hc : 0<c) (hh0 : (0:ℚ)≤h) (hh1 : h≤1)
    (hw : ∀ k : ℕ, k<5 → ∀ n : ℕ, n<80 →
      ‖ratComplexValue (w k n)-scaledPowerExpCoefficient (complexThetaExponent x)
        (c:ℂ) (Real.pi*((k:ℝ)+1)^2) h n‖≤1/(10:ℝ)^50) :
    |lowZeroThetaTaylorPanelValue x c h 80-(ratLowZeroApproxPanelValue h w:ℝ)|≤1600/(10:ℝ)^50 := by
  rw [ratLowZeroApproxPanelValue_cast]
  have he := lowZeroPanel_coefficient_error x c h (1/(10:ℝ)^50)
    (fun k n ↦ ratComplexValue (w k n)) hc (by exact_mod_cast hh0)
    (by exact_mod_cast hh1) (by positivity) (by
      intro k hk n hn
      rw [norm_sub_rev]
      exact hw k hk n hn)
  convert he using 1 <;> ring

def lowZeroStoredQuadrature (v : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8, v j i

theorem lowZeroStoredQuadrature_error (x : ℝ) (v : ℕ → ℕ → ℝ)
    (hv : ∀ j : ℕ, j<5 → ∀ i : ℕ, i<8 →
      |lowZeroThetaTaylorPanelValue x (theta48PanelCenter j i) (theta48PanelHalfWidth j) 80-
        v j i|≤1600/(10:ℝ)^50) :
    |lowZeroThetaQuadrature80 x-lowZeroStoredQuadrature v|≤64000/(10:ℝ)^50 := by
  unfold lowZeroThetaQuadrature80 lowZeroStoredQuadrature
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8,
      |lowZeroThetaTaylorPanelValue x (theta48PanelCenter j i) (theta48PanelHalfWidth j) 80-v j i| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun j hj ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _j ∈ Finset.range 5, ∑ _i ∈ Finset.range 8, 1600/(10:ℝ)^50 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact hv j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
    _ = _ := by norm_num

theorem F_lowZero_storedQuadrature_error (x : ℝ) (hx : |x|≤60)
    (v : ℕ → ℕ → ℝ)
    (hv : ∀ j : ℕ, j<5 → ∀ i : ℕ, i<8 →
      |lowZeroThetaTaylorPanelValue x (theta48PanelCenter j i) (theta48PanelHalfWidth j) 80-
        v j i|≤1600/(10:ℝ)^50) :
    |(F (x:ℂ)).re-(1-((1+x^2)/4)*lowZeroStoredQuadrature v)/8|≤4/(10:ℝ)^39 := by
  have hq := lowZeroStoredQuadrature_error x v hv
  have hf := F_lowZeroThetaQuadrature80_error x hx
  have hx2 : x^2≤3600 := by
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hx 2,sq_abs x]
  have ht := abs_sub_le (F (x:ℂ)).re ((1-((1+x^2)/4)*lowZeroThetaQuadrature80 x)/8)
    ((1-((1+x^2)/4)*lowZeroStoredQuadrature v)/8)
  have he : (1-((1+x^2)/4)*lowZeroThetaQuadrature80 x)/8-
      (1-((1+x^2)/4)*lowZeroStoredQuadrature v)/8=
      -((1+x^2)/32)*(lowZeroThetaQuadrature80 x-lowZeroStoredQuadrature v) := by ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤(1+x^2)/32)] at ht
  have hp := mul_le_mul_of_nonneg_left hq (show 0≤(1+x^2)/32 by positivity)
  have hc : (1+x^2)/32*(64000/(10:ℝ)^50)≤1/(10:ℝ)^39 := by nlinarith
  linarith

end ReciprocalXi



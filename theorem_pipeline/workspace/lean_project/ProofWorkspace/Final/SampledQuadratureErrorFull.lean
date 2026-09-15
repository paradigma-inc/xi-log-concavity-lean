import ProofWorkspace.Final.CosineQuadratureFull
import ProofWorkspace.Final.DensityCauchyBoundsFull

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

theorem complex_cos_norm_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z*Complex.I)) (Complex.exp (-z*Complex.I))
  rw [← Complex.two_cos, norm_mul] at h
  norm_num only [Complex.norm_ofNat] at h
  have hp : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
    exact neg_le_abs _
  have hn : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg]
    exact le_abs_self _
  linarith

theorem complex_cos_mul_real_norm_le (z : ℂ) (u q H : ℝ)
    (hq : |z.im| ≤ q) (hu : |u| ≤ H) :
    ‖Complex.cos (z*(u:ℂ))‖ ≤ Real.exp (q*H) := by
  apply (complex_cos_norm_le_exp_abs_im _).trans
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add,
    abs_mul]
  exact mul_le_mul hq hu (abs_nonneg _) ((abs_nonneg _).trans hq)

def sampledCosineQuadrature (z : ℂ) (h p : ℝ) (K : ℕ) (v : ℕ → ℝ) : ℂ :=
  (h/p) • ((v 0 / 2 : ℝ) + ∑ j ∈ Finset.range K,
    (v (j+1):ℂ) * Complex.cos (z*(h*((j:ℝ)+1):ℝ)))

theorem actual_cosine_quadrature_eq (z : ℂ) (h : ℝ) (K : ℕ) :
    finiteTrapezoid z h K =
      (h/Real.pi) • ((1/2:ℂ) + ∑ j ∈ Finset.range K,
        reciprocalTransform (h*((j:ℝ)+1)) * Complex.cos (z*(h*((j:ℝ)+1):ℝ))) := by
  rw [finiteTrapezoid_eq_cosine]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem sampledCosineQuadrature_error_le (z : ℂ) (h q H ε : ℝ) (K : ℕ)
    (v : ℕ → ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h) (hH : h*K ≤ H)
    (hq : |z.im| ≤ q) (hv0 : |1-v 0| ≤ ε)
    (hv : ∀ j ∈ Finset.range K,
      ‖reciprocalTransform (h*((j:ℝ)+1)) - (v (j+1):ℂ)‖ ≤ ε) :
    ‖finiteTrapezoid z h K - sampledCosineQuadrature z h Real.pi K v‖ ≤
      (h/Real.pi) * (ε/2 + (K:ℝ)*ε*Real.exp (q*H)) := by
  let a : ℕ → ℂ := fun j =>
    (reciprocalTransform (h*((j:ℝ)+1)) - (v (j+1):ℂ)) *
      Complex.cos (z*(h*((j:ℝ)+1):ℝ))
  have ha : ∀ j ∈ Finset.range K, ‖a j‖ ≤ ε * Real.exp (q*H) := by
    intro j hj
    have hjR : (j:ℝ)+1 ≤ K := by exact_mod_cast (Finset.mem_range.mp hj)
    have hu : |h*((j:ℝ)+1)| ≤ H := by
      rw [abs_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left hjR hh).trans hH
    dsimp only [a]
    rw [norm_mul]
    exact mul_le_mul (hv j hj) (complex_cos_mul_real_norm_le z _ q H hq hu)
      (norm_nonneg _) hε
  have hs : ‖∑ j ∈ Finset.range K, a j‖ ≤ (K:ℝ)*ε*Real.exp (q*H) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range K, ε*Real.exp (q*H) := Finset.sum_le_sum ha
      _ = _ := by simp; ring
  have hzero : ‖(1/2:ℂ) - ((v 0/2:ℝ):ℂ)‖ ≤ ε/2 := by
    have he : (1/2:ℂ) - ((v 0/2:ℝ):ℂ) = (((1-v 0)/2:ℝ):ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right hv0 (by norm_num)
  have hd : finiteTrapezoid z h K - sampledCosineQuadrature z h Real.pi K v =
      (h/Real.pi) • ((1/2:ℂ) - ((v 0/2:ℝ):ℂ) + ∑ j ∈ Finset.range K, a j) := by
    rw [actual_cosine_quadrature_eq]
    unfold sampledCosineQuadrature
    rw [← smul_sub]
    congr 1
    simp only [a, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hd, norm_smul, Real.norm_of_nonneg (div_nonneg hh Real.pi_pos.le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hh Real.pi_pos.le)
  exact (norm_add_le _ _).trans (add_le_add hzero hs)

theorem sampledCosineQuadrature_grid_error_lt (z : ℂ) (v : ℕ → ℝ)
    (hi : |z.im| ≤ 1/100) (hv0 : |1-v 0| ≤ 2/(10:ℝ)^120)
    (hv : ∀ j ∈ Finset.range 13600,
      ‖reciprocalTransform (((j:ℝ)+1)/40) - (v (j+1):ℂ)‖ ≤ 2/(10:ℝ)^120) :
    ‖finiteTrapezoid z (1/40) 13600 -
      sampledCosineQuadrature z (1/40) Real.pi 13600 v‖ < 2/(10:ℝ)^116 := by
  have he : Real.exp ((1/100:ℝ)*340) ≤ 81 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    exact (Real.exp_le_exp.mpr (by norm_num : (1/100:ℝ)*340 ≤ 4)).trans hp
  have hπ : (1/40:ℝ)/Real.pi ≤ 1/120 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have ht := sampledCosineQuadrature_error_le z (1/40) (1/100) 340
    (2/(10:ℝ)^120) 13600 v (by positivity) (by norm_num) (by norm_num) hi hv0
    (by
      intro j hj
      have he : (1/40:ℝ)*((j:ℝ)+1) = ((j:ℝ)+1)/40 := by ring
      rw [he]
      exact hv j hj)
  calc
    _ ≤ _ := ht
    _ ≤ (1/120:ℝ) * (2/(10:ℝ)^120/2 + 13600*(2/(10:ℝ)^120)*81) := by
      apply mul_le_mul hπ _ (by positivity) (by norm_num)
      gcongr
      norm_num
    _ < 2/(10:ℝ)^116 := by norm_num

theorem sampledCosineQuadrature_density_error_lt (z : ℂ) (v : ℕ → ℝ)
    (hr : |z.re| ≤ 4) (hi : |z.im| ≤ 1/100) (hv0 : |1-v 0| ≤ 2/(10:ℝ)^120)
    (hv : ∀ j ∈ Finset.range 13600,
      ‖reciprocalTransform (((j:ℝ)+1)/40) - (v (j+1):ℂ)‖ ≤ 2/(10:ℝ)^120) :
    ‖sampledCosineQuadrature z (1/40) Real.pi 13600 v - complexDensity z‖ <
      7/(8*(10:ℝ)^85) := by
  have hn := sampledCosineQuadrature_grid_error_lt z v hi hv0 hv
  have hq := finiteTrapezoid_error_grid_lt z hr hi
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sampledCosineQuadrature z (1/40) Real.pi 13600 v)
    (finiteTrapezoid z (1/40) 13600) (complexDensity z)
  rw [norm_sub_rev (sampledCosineQuadrature z (1/40) Real.pi 13600 v)
    (finiteTrapezoid z (1/40) 13600)] at ht
  have hb : 2/(10:ℝ)^116 + 3/(4*(10:ℝ)^85) < 7/(8*(10:ℝ)^85) := by norm_num
  linarith

theorem reciprocalTransform_norm_le_coarse (u : ℝ) :
    ‖reciprocalTransform u‖ ≤ 43046721 := by
  by_cases hu : |u| ≤ 3
  · exact (reciprocalTransform_norm_le_two_central u hu).trans (by norm_num)
  · have hp := reciprocalTransform_norm_le_exp_of_abs_three_le u (1/4) (le_of_not_ge hu)
    have hc := reciprocalTailConstant_quarter_le
    have he : Real.exp (-((1/4)*|u|)) ≤ 1 := by
      calc
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
        _ = 1 := Real.exp_zero
    have hb := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 16
    rw [← Real.exp_nat_mul] at hb
    norm_num at hb
    calc
      _ ≤ _ := hp
      _ ≤ Real.exp 16 * 1 := mul_le_mul hc he (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ 43046721 := by simpa only [mul_one] using hb

theorem approximate_sample_abs_le (u v ε : ℝ) (hε : ε ≤ 1)
    (hv : ‖reciprocalTransform u - (v:ℂ)‖ ≤ ε) : |v| ≤ 43046722 := by
  have ht := norm_le_norm_sub_add (v:ℂ) (reciprocalTransform u)
  rw [norm_sub_rev (v:ℂ) (reciprocalTransform u), Complex.norm_real, Real.norm_eq_abs] at ht
  linarith [reciprocalTransform_norm_le_coarse u]

theorem reciprocal_normalizer_error_le (p : ℝ) (hp : 3 ≤ p) :
    |(1/40:ℝ)/p - (1/40:ℝ)/Real.pi| ≤ |p-Real.pi| := by
  have hp0 : 0 < p := by linarith
  have he : (1/40:ℝ)/p - (1/40:ℝ)/Real.pi =
      ((1/40:ℝ)/(p*Real.pi)) * (Real.pi-p) := by
    field_simp
  rw [he, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
  have hb : (1/40:ℝ)/(p*Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg (p-Real.pi))

theorem sampledCosineQuadrature_pi_error_lt (z : ℂ) (v : ℕ → ℝ) (p : ℝ)
    (hi : |z.im| ≤ 1/100) (hp : 3 ≤ p) (hpπ : |p-Real.pi| ≤ 1/(10:ℝ)^150)
    (hv : ∀ k ≤ 13600, |v k| ≤ 100000000) :
    ‖sampledCosineQuadrature z (1/40) p 13600 v -
      sampledCosineQuadrature z (1/40) Real.pi 13600 v‖ < 1/(10:ℝ)^115 := by
  have he : Real.exp ((1/100:ℝ)*340) ≤ 81 := by
    have ht := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_nat_mul] at ht
    norm_num at ht
    exact (Real.exp_le_exp.mpr (by norm_num : (1/100:ℝ)*340 ≤ 4)).trans ht
  have ha : ∀ j ∈ Finset.range 13600,
      ‖(v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 8100000000 := by
    intro j hj
    have hjN : j+1 ≤ 13600 := Finset.mem_range.mp hj
    have hjR : (j:ℝ)+1 ≤ 13600 := by exact_mod_cast hjN
    have hu : |(1/40:ℝ)*((j:ℝ)+1)| ≤ 340 := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hc := (complex_cos_mul_real_norm_le z _ (1/100) 340 hi hu).trans he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ht := mul_le_mul (hv (j+1) hjN) hc (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 100000000)
    norm_num at ht ⊢
    exact ht
  have hs : ‖∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 110160000000000 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range 13600, (8100000000:ℝ) := Finset.sum_le_sum ha
      _ = _ := by simp; norm_num
  have hz : ‖((v 0/2:ℝ):ℂ)‖ ≤ 50000000 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    have ht := div_le_div_of_nonneg_right (hv 0 (by omega)) (by norm_num : (0:ℝ) ≤ 2)
    norm_num at ht ⊢
    exact ht
  have hn := norm_add_le ((v 0/2:ℝ):ℂ)
    (∑ j ∈ Finset.range 13600, (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ)))
  have hm : ‖((v 0/2:ℝ):ℂ) + ∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 110160050000000 := by linarith
  unfold sampledCosineQuadrature
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hd := (reciprocal_normalizer_error_le p hp).trans hpπ
  calc
    _ ≤ (1/(10:ℝ)^150)*110160050000000 := mul_le_mul hd hm (norm_nonneg _) (by positivity)
    _ < 1/(10:ℝ)^115 := by norm_num

theorem reciprocalTransform_sample_norm_eq_abs (u v : ℝ) :
    ‖reciprocalTransform u - (v:ℂ)‖ = |(reciprocalTransform u).re-v| := by
  have he := (Complex.conj_eq_iff_re.mp (reciprocalTransform_conj u)).symm
  conv_lhs => rw [he]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem sampledCosineQuadrature_source_error_lt (z : ℂ) (v : ℕ → ℝ) (p : ℝ)
    (hr : |z.re| ≤ 4) (hi : |z.im| ≤ 1/100)
    (hp : 3 ≤ p) (hpπ : |p-Real.pi| ≤ 1/(10:ℝ)^150)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledCosineQuadrature z (1/40) p 13600 v - complexDensity z‖ <
      1/(10:ℝ)^85 := by
  have hvC : ∀ (k : ℕ), k ≤ 13600 →
      ‖reciprocalTransform ((k:ℝ)/40) - (v k:ℂ)‖ ≤ 2/(10:ℝ)^120 := by
    intro k hk
    rw [reciprocalTransform_sample_norm_eq_abs]
    exact hv k hk
  have hv0 : |1-v 0| ≤ 2/(10:ℝ)^120 := by
    have ht := hv 0 (by omega)
    simpa only [Nat.cast_zero, zero_div, reciprocalTransform_zero, Complex.one_re] using ht
  have hvS : ∀ j ∈ Finset.range 13600,
      ‖reciprocalTransform (((j:ℝ)+1)/40) - (v (j+1):ℂ)‖ ≤ 2/(10:ℝ)^120 := by
    intro j hj
    simpa only [Nat.cast_add, Nat.cast_one] using hvC (j+1) (Finset.mem_range.mp hj)
  have hvB : ∀ k ≤ 13600, |v k| ≤ 100000000 := by
    intro k hk
    exact (approximate_sample_abs_le _ _ _ (by norm_num : 2/(10:ℝ)^120 ≤ 1)
      (hvC k hk)).trans (by norm_num)
  have hA := sampledCosineQuadrature_density_error_lt z v hr hi hv0 hvS
  have hpA := sampledCosineQuadrature_pi_error_lt z v p hi hp hpπ hvB
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sampledCosineQuadrature z (1/40) p 13600 v)
    (sampledCosineQuadrature z (1/40) Real.pi 13600 v) (complexDensity z)
  have hb : 1/(10:ℝ)^115 + 7/(8*(10:ℝ)^85) < 1/(10:ℝ)^85 := by norm_num
  linarith

theorem differentiable_sampledCosineQuadrature (h p : ℝ) (K : ℕ) (v : ℕ → ℝ) :
    Differentiable ℂ (fun z => sampledCosineQuadrature z h p K v) := by
  unfold sampledCosineQuadrature
  fun_prop

def normalizedSampleError (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) : ℂ :=
  complexDensity ((c:ℂ) + (1/200:ℂ)*z) -
    sampledCosineQuadrature ((c:ℂ) + (1/200:ℂ)*z) (1/40) p 13600 v

theorem differentiable_normalizedSampleError (c p : ℝ) (v : ℕ → ℝ) :
    Differentiable ℂ (normalizedSampleError c p v) := by
  have hA := differentiable_sampledCosineQuadrature (1/40) p 13600 v
  have hG := differentiable_complexDensity
  unfold normalizedSampleError
  fun_prop

theorem normalizedSampleError_jet_le (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hc : |c| ≤ 318/100) (hx : |x| ≤ 1) (hn : n ≤ 2)
    (hp : 3 ≤ p) (hpπ : |p-Real.pi| ≤ 1/(10:ℝ)^150)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (normalizedSampleError c p v) (x:ℂ)‖ ≤ 8/(10:ℝ)^85 := by
  have hbound : ∀ w ∈ Metric.sphere (x:ℂ) (1/2),
      ‖normalizedSampleError c p v w‖ ≤ 1/(10:ℝ)^85 := by
    intro w hw
    have hd := Metric.mem_sphere.mp hw
    rw [dist_eq_norm] at hd
    have ht := norm_le_norm_sub_add w (x:ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    have hwN : ‖w‖ ≤ 3/2 := by linarith
    have hwR : |w.re| ≤ 3/2 := (Complex.abs_re_le_norm w).trans hwN
    have hwI : |w.im| ≤ 3/2 := (Complex.abs_im_le_norm w).trans hwN
    have hr : |((c:ℂ) + (1/200:ℂ)*w).re| ≤ 4 := by
      have hRe : ((c:ℂ) + (1/200:ℂ)*w).re = c+(1/200:ℝ)*w.re := by
        norm_num [Complex.mul_re]
      rw [hRe]
      have ht := abs_add_le c ((1/200:ℝ)*w.re)
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/200)] at ht
      nlinarith
    have hi : |((c:ℂ) + (1/200:ℂ)*w).im| ≤ 1/100 := by
      have hIm : ((c:ℂ) + (1/200:ℂ)*w).im = (1/200:ℝ)*w.im := by
        norm_num [Complex.mul_im]
      rw [hIm]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/200)]
      nlinarith
    unfold normalizedSampleError
    rw [norm_sub_rev]
    exact (sampledCosineQuadrature_source_error_lt _ v p hr hi hp hpπ hv).le
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/2) (differentiable_normalizedSampleError c p v).diffContOnCl hbound
  apply hb.trans
  interval_cases n <;> norm_num [Nat.factorial]

end ReciprocalXi


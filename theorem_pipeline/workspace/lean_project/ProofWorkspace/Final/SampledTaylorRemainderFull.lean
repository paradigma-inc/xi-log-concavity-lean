import ProofWorkspace.Final.SampledQuadratureDiskFull
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

theorem sampledCosineQuadrature_large_strip_coarse (z : ℂ) (v : ℕ → ℝ) (p : ℝ)
    (hi : |z.im| ≤ 1/4) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledCosineQuadrature z (1/40) p 13600 v‖ < 5000000000 := by
  have he : (2/(10:ℝ)^120)*Real.exp 85 ≤ 1 := by
    have ht := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 85
    rw [← Real.exp_nat_mul] at ht
    norm_num only [Nat.cast_ofNat, mul_one] at ht
    calc
      _ ≤ (2/(10:ℝ)^120)*(3:ℝ)^85 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at ht ⊢
        exact ht
      _ ≤ 1 := by norm_num
  have hvC : ∀ (k : ℕ), k ≤ 13600 →
      ‖reciprocalTransform ((k:ℝ)/40) - (v k:ℂ)‖ ≤ 2/(10:ℝ)^120 := by
    intro k hk
    rw [reciprocalTransform_sample_norm_eq_abs]
    exact hv k hk
  have ha : ∀ j ∈ Finset.range 13600,
      ‖(v (j+1):ℂ) * Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 43046722 := by
    intro j hj
    let u : ℝ := (1/40)*((j:ℝ)+1)
    have hu : |u| ≤ 340 := by
      have hjR : (j:ℝ)+1 ≤ 13600 := by exact_mod_cast (Finset.mem_range.mp hj)
      dsimp only [u]
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hcos : ‖Complex.cos (z*(u:ℂ))‖ ≤ Real.exp 85 := by
      have ht := complex_cos_mul_real_norm_le z u (1/4) 340 hi hu
      norm_num at ht
      exact ht
    have hsample : ‖reciprocalTransform u - (v (j+1):ℂ)‖ ≤ 2/(10:ℝ)^120 := by
      have huEq : u = ((j+1:ℕ):ℝ)/40 := by dsimp [u]; push_cast; ring
      rw [huEq]
      exact hvC (j+1) (Finset.mem_range.mp hj)
    have hdiff : ‖(reciprocalTransform u - (v (j+1):ℂ))*Complex.cos (z*(u:ℂ))‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul hsample hcos (norm_nonneg _) (by positivity)).trans he
    have ht := norm_le_norm_sub_add ((v (j+1):ℂ)*Complex.cos (z*(u:ℂ)))
      (reciprocalTransform u*Complex.cos (z*(u:ℂ)))
    rw [norm_sub_rev, ← sub_mul] at ht
    have hb := reciprocal_cosine_norm_le_coarse z u hi
    change ‖(v (j+1):ℂ)*Complex.cos (z*(u:ℂ))‖ ≤ 43046722
    linarith
  have hsum : ‖∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 13600*(43046722:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range 13600, (43046722:ℝ) := Finset.sum_le_sum ha
      _ = _ := by simp
  have hv0 : |v 0| ≤ 2 := by
    have ht := hv 0 (by omega)
    simp only [Nat.cast_zero, zero_div, reciprocalTransform_zero, Complex.one_re] at ht
    have hδ : 2/(10:ℝ)^120 ≤ 1 := by norm_num
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hz : ‖((v 0/2:ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    norm_num
    linarith
  have hn : ‖((v 0/2:ℝ):ℂ) + ∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 1+13600*(43046722:ℝ) :=
    (norm_add_le _ _).trans (add_le_add hz hsum)
  have hp0 : 0 < p := by linarith
  have hnorm : (1/40:ℝ)/p ≤ 1/120 := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  unfold sampledCosineQuadrature
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (1/120:ℝ)*(1+13600*43046722) := mul_le_mul hnorm hn (norm_nonneg _) (by norm_num)
    _ < 5000000000 := by norm_num


theorem normalizedSampledQuadrature_disk_coarse (c p : ℝ) (v : ℕ → ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 50) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖normalizedSampledQuadrature c p v z‖ < 5000000000 := by
  apply sampledCosineQuadrature_large_strip_coarse _ v p _ hp hv
  have hIm : ((c:ℂ)+(1/200:ℂ)*z).im = (1/200:ℝ)*z.im := by
    norm_num [Complex.mul_im]
  rw [hIm, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/200)]
  have hi := (Complex.abs_im_le_norm z).trans hz
  linarith

theorem sampledTaylorCoefficient_norm_le_coarse (c p : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledTaylorCoefficient c p v n‖ ≤ 5000000000/(50:ℝ)^n := by
  have hF : ∀ w ∈ Metric.sphere (0:ℂ) 50,
      ‖normalizedSampledQuadrature c p v w‖ ≤ 5000000000 := by
    intro w hw
    have hn : ‖w‖ = 50 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact (normalizedSampledQuadrature_disk_coarse c p v w hn.le hp hv).le
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<50) (differentiable_normalizedSampledQuadrature c p v).diffContOnCl hF
  have hn : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hm := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  unfold sampledTaylorCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert hm using 1
  field_simp

def sampledTaylorPolynomial64 (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 65, sampledTaylorCoefficient c p v n * z^n

theorem differentiable_sampledTaylorPolynomial64 (c p : ℝ) (v : ℕ → ℝ) :
    Differentiable ℂ (sampledTaylorPolynomial64 c p v) := by
  unfold sampledTaylorPolynomial64
  fun_prop

def sampledTaylorRemainder64 (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) : ℂ :=
  normalizedSampledQuadrature c p v z - sampledTaylorPolynomial64 c p v z

theorem differentiable_sampledTaylorRemainder64 (c p : ℝ) (v : ℕ → ℝ) :
    Differentiable ℂ (sampledTaylorRemainder64 c p v) := by
  have hA := differentiable_normalizedSampledQuadrature c p v
  unfold sampledTaylorRemainder64 sampledTaylorPolynomial64
  fun_prop

theorem sampledTaylor_term_norm_le_coarse (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) (n : ℕ)
    (hz : ‖z‖ ≤ 3/2) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledTaylorCoefficient c p v n * z^n‖ ≤ 5000000000*(3/100:ℝ)^n := by
  rw [norm_mul, norm_pow]
  have ht := mul_le_mul (sampledTaylorCoefficient_norm_le_coarse c p v n hp hv)
    (pow_le_pow_left₀ (norm_nonneg z) hz n) (pow_nonneg (norm_nonneg z) n) (by positivity)
  calc
    _ ≤ (5000000000/(50:ℝ)^n)*(3/2:ℝ)^n := ht
    _ = 5000000000*((3/2:ℝ)/50)^n := by
      conv_rhs => rw [div_pow]
      ring
    _ = _ := by norm_num

theorem sampledTaylorRemainder64_disk_le (c p : ℝ) (v : ℕ → ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 3/2) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledTaylorRemainder64 c p v z‖ ≤
      5000000000*(3/100:ℝ)^65/(1-3/100) := by
  have ht := (hasSum_nat_add_iff' 65).mpr (hasSum_sampledTaylor c p v z)
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/100)
    (by norm_num : (3/100:ℝ)<1)).mul_left (5000000000*(3/100:ℝ)^65)
  have hb : ∀ n : ℕ, ‖sampledTaylorCoefficient c p v (n+65)*z^(n+65)‖ ≤
      5000000000*(3/100:ℝ)^65*(3/100:ℝ)^n := by
    intro n
    have h := sampledTaylor_term_norm_le_coarse c p v z (n+65) hz hp hv
    convert h using 1
    rw [pow_add]
    ring
  have h := ht.norm_le_of_bounded hg hb
  simpa only [sampledTaylorRemainder64, sampledTaylorPolynomial64, div_eq_mul_inv] using h

def sourceTaylorTau : ℝ :=
  Real.exp 66*(1/50:ℝ)^65*(66:ℝ)^2/(1-1/50)^3

theorem sourceTaylorTau_ge_geometric :
    8*(5000000000*(3/100:ℝ)^65/(1-3/100)) ≤ sourceTaylorTau := by
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le 66
  rw [←Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  unfold sourceTaylorTau
  have hq : 8*(5000000000*(3/100:ℝ)^65/(1-3/100)) ≤
      (2:ℝ)^66*(1/50)^65*66^2/(1-1/50)^3 := by norm_num
  exact hq.trans (by gcongr; norm_num at he ⊢; exact he)

theorem sampledTaylorRemainder64_jet_le (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hx : |x| ≤ 1) (hn : n ≤ 2) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (sampledTaylorRemainder64 c p v) (x:ℂ)‖ ≤ sourceTaylorTau := by
  have hbound : ∀ w ∈ Metric.sphere (x:ℂ) (1/2),
      ‖sampledTaylorRemainder64 c p v w‖ ≤
        5000000000*(3/100:ℝ)^65/(1-3/100) := by
    intro w hw
    have hd := Metric.mem_sphere.mp hw
    rw [dist_eq_norm] at hd
    have ht := norm_le_norm_sub_add w (x:ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    have hwN : ‖w‖ ≤ 3/2 := by linarith
    exact sampledTaylorRemainder64_disk_le c p v w hwN hp hv
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/2) (differentiable_sampledTaylorRemainder64 c p v).diffContOnCl hbound
  apply hb.trans
  apply le_trans _ sourceTaylorTau_ge_geometric
  interval_cases n <;> norm_num [Nat.factorial]

theorem sampledTaylorPolynomial64_jet_error_le (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hx : |x| ≤ 1) (hn : n ≤ 2) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re-v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (normalizedSampledQuadrature c p v) (x:ℂ) -
      iteratedDeriv n (sampledTaylorPolynomial64 c p v) (x:ℂ)‖ ≤ sourceTaylorTau := by
  have hA : ContDiffAt ℂ n (normalizedSampledQuadrature c p v) (x:ℂ) :=
    (differentiable_normalizedSampledQuadrature c p v).contDiff.contDiffAt
  have hP : ContDiffAt ℂ n (sampledTaylorPolynomial64 c p v) (x:ℂ) :=
    (differentiable_sampledTaylorPolynomial64 c p v).contDiff.contDiffAt
  have h := sampledTaylorRemainder64_jet_le c p x v n hx hn hp hv
  unfold sampledTaylorRemainder64 at h
  rw [iteratedDeriv_fun_sub hA hP] at h
  exact h

end ReciprocalXi


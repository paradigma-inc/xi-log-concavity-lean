import ProofWorkspace.Final.SampledTaylorRemainderFull
import ProofWorkspace.Final.SourcePiMidpointFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def normalizedComplexDensity (c : ℝ) (z : ℂ) : ℂ :=
  complexDensity ((c:ℂ)+(1/200:ℂ)*z)

theorem differentiable_normalizedComplexDensity (c : ℝ) :
    Differentiable ℂ (normalizedComplexDensity c) := by
  have hG := differentiable_complexDensity
  unfold normalizedComplexDensity
  fun_prop

def sourcePanelJetError : ℝ := 8/(10:ℝ)^85 + sourceTaylorTau

theorem sourcePanelJetError_nonneg : 0 ≤ sourcePanelJetError := by
  unfold sourcePanelJetError sourceTaylorTau
  positivity

theorem normalizedComplexDensity_sample_error_le (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hc : |c| ≤ 318/100) (hx : |x| ≤ 1) (hn : n ≤ 2)
    (hp : 3 ≤ p) (hpπ : |p-Real.pi| ≤ 1/(10:ℝ)^150)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (normalizedComplexDensity c) (x:ℂ) -
      iteratedDeriv n (normalizedSampledQuadrature c p v) (x:ℂ)‖ ≤ 8/(10:ℝ)^85 := by
  have hD : ContDiffAt ℂ n (normalizedComplexDensity c) (x:ℂ) :=
    (differentiable_normalizedComplexDensity c).contDiff.contDiffAt
  have hA : ContDiffAt ℂ n (normalizedSampledQuadrature c p v) (x:ℂ) :=
    (differentiable_normalizedSampledQuadrature c p v).contDiff.contDiffAt
  have heq : normalizedSampleError c p v =
      fun z => normalizedComplexDensity c z - normalizedSampledQuadrature c p v z := rfl
  have h := normalizedSampleError_jet_le c p x v n hc hx hn hp hpπ hv
  rw [heq, iteratedDeriv_fun_sub hD hA] at h
  exact h

theorem normalizedComplexDensity_taylor_error_le (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hc : |c| ≤ 318/100) (hx : |x| ≤ 1) (hn : n ≤ 2)
    (hp : 3 ≤ p) (hpπ : |p-Real.pi| ≤ 1/(10:ℝ)^150)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (normalizedComplexDensity c) (x:ℂ) -
      iteratedDeriv n (sampledTaylorPolynomial64 c p v) (x:ℂ)‖ ≤ sourcePanelJetError := by
  have hDA := normalizedComplexDensity_sample_error_le c p x v n hc hx hn hp hpπ hv
  have hAP := sampledTaylorPolynomial64_jet_error_le c p x v n hx hn hp hv
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (iteratedDeriv n (normalizedComplexDensity c) (x:ℂ))
    (iteratedDeriv n (normalizedSampledQuadrature c p v) (x:ℂ))
    (iteratedDeriv n (sampledTaylorPolynomial64 c p v) (x:ℂ))
  exact ht.trans (add_le_add hDA hAP)

theorem normalizedComplexDensity_source_taylor_error_le (c x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hc : |c| ≤ 318/100) (hx : |x| ≤ 1) (hn : n ≤ 2)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖iteratedDeriv n (normalizedComplexDensity c) (x:ℂ) -
      iteratedDeriv n (sampledTaylorPolynomial64 c sourcePiMidpoint v) (x:ℂ)‖ ≤
      sourcePanelJetError := by
  exact normalizedComplexDensity_taylor_error_le c sourcePiMidpoint x v n hc hx hn
    (by exact_mod_cast sourcePiMidpoint_ge_three) sourcePiMidpoint_error hv

theorem normalizedComplexDensity_source_taylor_re_error_le (c x : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hc : |c| ≤ 318/100) (hx : |x| ≤ 1) (hn : n ≤ 2)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    |(iteratedDeriv n (normalizedComplexDensity c) (x:ℂ)).re -
      (iteratedDeriv n (sampledTaylorPolynomial64 c sourcePiMidpoint v) (x:ℂ)).re| ≤
      sourcePanelJetError := by
  exact (Complex.abs_re_le_norm _).trans
    (normalizedComplexDensity_source_taylor_error_le c x v n hc hx hn hv)

end ReciprocalXi


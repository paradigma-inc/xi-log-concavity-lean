import ProofWorkspace.Final.SourceCoefficientStreamFull
import ProofWorkspace.Final.ActualPanelEnclosuresFull
import ProofWorkspace.Final.RoundedTaylorBoundsFull

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

theorem sum_abs_coeff_le_coefficientNorm (p : Polynomial ℝ) (s : Finset ℕ) :
    (∑ j ∈ s, |p.coeff j|) ≤ coefficientNorm p := by
  have he : coefficientNorm p = ∑ j ∈ s ∪ p.support, |p.coeff j| := by
    exact p.sum_eq_of_subset (fun _ a => |a|) (fun _ => abs_zero) Finset.subset_union_right
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun _ _ _ => abs_nonneg _)

theorem coefficientNorm_add_le (p q : Polynomial ℝ) :
    coefficientNorm (p+q) ≤ coefficientNorm p + coefficientNorm q := by
  unfold coefficientNorm at ⊢
  calc
    _ ≤ ∑ j ∈ (p+q).support, (|p.coeff j|+|q.coeff j|) := by
      apply Finset.sum_le_sum
      intro j _
      rw [Polynomial.coeff_add]
      exact abs_add_le _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (sum_abs_coeff_le_coefficientNorm p _)
      (sum_abs_coeff_le_coefficientNorm q _)

theorem coefficientNorm_neg (p : Polynomial ℝ) : coefficientNorm (-p) = coefficientNorm p := by
  simp [coefficientNorm]

theorem coefficientNorm_sub_le (p q : Polynomial ℝ) :
    coefficientNorm (p-q) ≤ coefficientNorm p + coefficientNorm q := by
  simpa only [sub_eq_add_neg, coefficientNorm_neg] using coefficientNorm_add_le p (-q)

theorem coefficientNorm_monomial (j : ℕ) (a : ℝ) :
    coefficientNorm (Polynomial.monomial j a) = |a| := by
  by_cases ha : a=0
  · simp [ha, coefficientNorm]
  · simp [coefficientNorm, Polynomial.support_monomial j ha]

theorem coefficientNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    coefficientNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientNorm]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (coefficientNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem coefficientNorm_mul_le (p q : Polynomial ℝ) :
    coefficientNorm (p*q) ≤ coefficientNorm p * coefficientNorm q := by
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  apply (coefficientNorm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, |p.coeff i*q.coeff j| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [coefficientNorm_monomial] using
        coefficientNorm_sum_le q.support (fun j => Polynomial.monomial (i+j) (p.coeff i*q.coeff j))
    _ = _ := by simp only [abs_mul, ← Finset.mul_sum, ← Finset.sum_mul, coefficientNorm]

def panelCoefficientPolynomial (f : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range 65, Polynomial.monomial j (f j)

private theorem panel_sum_monomial_norm_le (f : ℕ → ℝ) (d : ℕ → ℕ)
    (M : ℝ) (hf : ∀ j, j < 65 → |f j| ≤ M) :
    coefficientNorm (∑ j ∈ Finset.range 65, Polynomial.monomial (d j) (f j)) ≤ 65*M := by
  calc
    _ ≤ ∑ j ∈ Finset.range 65, coefficientNorm (Polynomial.monomial (d j) (f j)) :=
      coefficientNorm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range 65, M := by
      apply Finset.sum_le_sum
      intro j hj
      rw [coefficientNorm_monomial]
      exact hf j (Finset.mem_range.mp hj)
    _ = 65*M := by simp

theorem panelCoefficientPolynomial_jetNorm_bounds (f : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hf : ∀ j, j < 65 → |f j| ≤ δ) :
    coefficientNorm (panelCoefficientPolynomial f) ≤ 65*δ ∧
    coefficientNorm (panelCoefficientPolynomial f).derivative ≤ 65*(δ*64) ∧
    coefficientNorm (panelCoefficientPolynomial f).derivative.derivative ≤ 65*(δ*64*63) := by
  have h1 : ∀ j, j < 65 → |f j*(j:ℝ)| ≤ δ*64 := by
    intro j hj
    have habs : |(j:ℝ)| = (j:ℝ) := abs_of_nonneg (Nat.cast_nonneg j)
    rw [abs_mul, habs]
    have hj' : (j:ℝ) ≤ 64 := by exact_mod_cast (show j ≤ 64 by omega)
    exact mul_le_mul (hf j hj) hj' (Nat.cast_nonneg _) hδ
  have h2 : ∀ j, j < 65 → |(f j*(j:ℝ))*((j-1:ℕ):ℝ)| ≤ δ*64*63 := by
    intro j hj
    have habs : |((j-1:ℕ):ℝ)| = ((j-1:ℕ):ℝ) := abs_of_nonneg (Nat.cast_nonneg (j-1))
    rw [abs_mul, habs]
    have hj' : ((j-1:ℕ):ℝ) ≤ 63 := by exact_mod_cast (show j-1 ≤ 63 by omega)
    exact mul_le_mul (h1 j hj) hj' (Nat.cast_nonneg _) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · exact panel_sum_monomial_norm_le f id δ hf
  · simpa only [panelCoefficientPolynomial, Polynomial.derivative_sum,
      Polynomial.derivative_monomial] using
      panel_sum_monomial_norm_le (fun j => f j*(j:ℝ)) (fun j => j-1) (δ*64) h1
  · simpa only [panelCoefficientPolynomial, Polynomial.derivative_sum,
      Polynomial.derivative_monomial] using
      panel_sum_monomial_norm_le (fun j => (f j*(j:ℝ))*((j-1:ℕ):ℝ))
        (fun j => j-1-1) (δ*64*63) h2

def ratSourceCoefficientBudget : ℚ :=
  13601*(1/(sourceCoefficientScale:ℚ)+2*((2:ℚ)^65/(sourceCoefficientScale:ℚ))+
    (43046722*(2:ℚ)^64)*(18*13600/(sourceCoefficientScale:ℚ)))

theorem ratSourceCoefficientBudget_cast :
    (ratSourceCoefficientBudget:ℝ) = 13601*sourceRoundedCoefficientTermBudget := by
  simp only [ratSourceCoefficientBudget, sourceRoundedCoefficientTermBudget,
    Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one]

theorem ratSourceCoefficientBudget_nonneg : 0 ≤ ratSourceCoefficientBudget := by
  unfold ratSourceCoefficientBudget
  positivity

def ratSourcePanelJetUpper : ℚ :=
  8/(10:ℚ)^85 + ratExpFullyRoundedUpper 66 128 128 (10^180) *
    (1/50:ℚ)^65*66^2/(1-1/50:ℚ)^3

theorem sourcePanelJetError_le_ratUpper :
    sourcePanelJetError ≤ (ratSourcePanelJetUpper:ℝ) := by
  have he := (ratExpFullyRounded_enclosure 66 128 128 (10^180)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  norm_num only [Rat.cast_ofNat] at he
  unfold sourcePanelJetError sourceTaylorTau ratSourcePanelJetUpper
  push_cast
  gcongr

theorem ratSourcePanelJetUpper_nonneg : 0 ≤ ratSourcePanelJetUpper := by
  have he : 0 ≤ (ratSourcePanelJetUpper:ℝ) :=
    sourcePanelJetError_nonneg.trans sourcePanelJetError_le_ratUpper
  exact (Rat.cast_nonneg (K := ℝ)).mp he

def ratPanelCoefficient (a : List ℤ) (j : ℕ) : ℚ := sourceGridDecode ((a[j]?).getD 0)

def ratPanelPolynomial (a : List ℤ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range 65, Polynomial.monomial j (ratPanelCoefficient a j)

def realPanelPolynomial (a : List ℤ) : Polynomial ℝ :=
  (ratPanelPolynomial a).map (Rat.castHom ℝ)

theorem realPanelPolynomial_eq (a : List ℤ) :
    realPanelPolynomial a = panelCoefficientPolynomial (fun j => (ratPanelCoefficient a j:ℝ)) := by
  unfold realPanelPolynomial ratPanelPolynomial panelCoefficientPolynomial
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_monomial]
  rfl

theorem ratPanelCoefficient_stream_eq (c p : ℚ) (v : ℕ → ℚ) (j : ℕ) (hj : j < 65) :
    ratPanelCoefficient (intSourceCoefficientStream c p v) j = ratSourceRoundedCoefficient c p v j := by
  have hl : j < (intSourceCoefficientStream c p v).length := by
    rw [intSourceCoefficientStream_length]
    exact hj
  unfold ratPanelCoefficient
  rw [List.getElem?_eq_getElem hl, Option.getD_some]
  exact ratSourceStreamCoefficient_eq c p v ⟨j,hj⟩

theorem realSampledTaylorPolynomial_coeff_lt (c p : ℝ) (v : ℕ → ℝ) (j : ℕ) (hj : j < 65) :
    (realSampledTaylorPolynomial c p v).coeff j = (sampledTaylorCoefficient c p v j).re := by
  simp [realSampledTaylorPolynomial, Polynomial.coeff_monomial, hj]

theorem sampledPolynomial_sub_realPanel (c p : ℝ) (v : ℕ → ℝ) (a : List ℤ) :
    realSampledTaylorPolynomial c p v - realPanelPolynomial a =
      panelCoefficientPolynomial (fun j => (sampledTaylorCoefficient c p v j).re -
        (ratPanelCoefficient a j:ℝ)) := by
  rw [realPanelPolynomial_eq]
  unfold realSampledTaylorPolynomial panelCoefficientPolynomial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.monomial_sub]

def ratCoefficientNorm (p : Polynomial ℚ) : ℚ := ∑ j ∈ p.support, |p.coeff j|

theorem coefficientNorm_map_rat (p : Polynomial ℚ) :
    coefficientNorm (p.map (Rat.castHom ℝ)) = (ratCoefficientNorm p:ℝ) := by
  unfold coefficientNorm ratCoefficientNorm
  rw [Polynomial.support_map_of_injective p (Rat.cast_injective)]
  simp only [Polynomial.coeff_map, Rat.cast_sum, Rat.cast_abs]
  rfl

def ratCurvaturePolynomial (p : Polynomial ℚ) : Polynomial ℚ :=
  p.derivative^2-p*p.derivative.derivative

theorem curvaturePolynomial_map_rat (p : Polynomial ℚ) :
    curvaturePolynomial (p.map (Rat.castHom ℝ)) = (ratCurvaturePolynomial p).map (Rat.castHom ℝ) := by
  simp [curvaturePolynomial, ratCurvaturePolynomial, Polynomial.derivative_map]

theorem erase_zero_map_rat (p : Polynomial ℚ) :
    (p.map (Rat.castHom ℝ)).erase 0 = (p.erase 0).map (Rat.castHom ℝ) := by
  ext j
  by_cases hj : j=0 <;> simp [Polynomial.coeff_erase, hj]

theorem abs_coeff_le_coefficientNorm (p : Polynomial ℝ) (j : ℕ) :
    |p.coeff j| ≤ coefficientNorm p := by
  simpa only [Finset.sum_singleton] using sum_abs_coeff_le_coefficientNorm p {j}

theorem coefficientNorm_erase_zero_le (p : Polynomial ℝ) :
    coefficientNorm (p.erase 0) ≤ coefficientNorm p := by
  rw [coefficientNorm_erase_zero]
  exact sum_abs_coeff_le_coefficientNorm p (p.support.erase 0)

theorem coefficientNorm_le_of_sub (p a : Polynomial ℝ) (d : ℝ)
    (h : coefficientNorm (p-a) ≤ d) : coefficientNorm p ≤ coefficientNorm a+d := by
  have he : p = a+(p-a) := by ring
  calc
    coefficientNorm p = coefficientNorm (a+(p-a)) := congrArg coefficientNorm he
    _ ≤ coefficientNorm a+coefficientNorm (p-a) := coefficientNorm_add_le _ _
    _ ≤ _ := add_le_add le_rfl h

theorem curvaturePolynomial_coefficientNorm_difference (p a : Polynomial ℝ)
    (d0 d1 d2 : ℝ) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h0 : coefficientNorm (p-a) ≤ d0)
    (h1 : coefficientNorm (p.derivative-a.derivative) ≤ d1)
    (h2 : coefficientNorm (p.derivative.derivative-a.derivative.derivative) ≤ d2) :
    coefficientNorm (curvaturePolynomial p-curvaturePolynomial a) ≤
      d1*(2*coefficientNorm a.derivative+d1)+
        d0*(coefficientNorm a.derivative.derivative+d2)+coefficientNorm a*d2 := by
  have hn1 := coefficientNorm_le_of_sub p.derivative a.derivative d1 h1
  have hn2 := coefficientNorm_le_of_sub p.derivative.derivative a.derivative.derivative d2 h2
  have hsum : coefficientNorm (p.derivative+a.derivative) ≤ 2*coefficientNorm a.derivative+d1 := by
    have h := coefficientNorm_add_le p.derivative a.derivative
    linarith
  have he : curvaturePolynomial p-curvaturePolynomial a =
      (p.derivative-a.derivative)*(p.derivative+a.derivative)-
        (p-a)*p.derivative.derivative-a*(p.derivative.derivative-a.derivative.derivative) := by
    unfold curvaturePolynomial
    ring
  rw [he]
  apply (coefficientNorm_sub_le _ _).trans
  apply add_le_add
  · apply (coefficientNorm_sub_le _ _).trans
    apply add_le_add
    · exact (coefficientNorm_mul_le _ _).trans
        (mul_le_mul h1 hsum (coefficientNorm_nonneg _) hd1)
    · exact (coefficientNorm_mul_le _ _).trans
        (mul_le_mul h0 hn2 (coefficientNorm_nonneg _) hd0)
  · exact (coefficientNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left h2 (coefficientNorm_nonneg _))

theorem sampled_stream_jetNorm_difference (c p : ℚ) (v : ℕ → ℚ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 40) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(v k:ℝ)| ≤ 43046722) :
    let P := realSampledTaylorPolynomial (c:ℝ) (p:ℝ) (fun k => (v k:ℝ))
    let A := realPanelPolynomial (intSourceCoefficientStream c p v)
    coefficientNorm (P-A) ≤ 65*(ratSourceCoefficientBudget:ℝ) ∧
    coefficientNorm (P.derivative-A.derivative) ≤ 65*((ratSourceCoefficientBudget:ℝ)*64) ∧
    coefficientNorm (P.derivative.derivative-A.derivative.derivative) ≤
      65*((ratSourceCoefficientBudget:ℝ)*64*63) := by
  dsimp only
  have hδ : (0:ℝ) ≤ ratSourceCoefficientBudget :=
    (Rat.cast_nonneg (K := ℝ)).mpr ratSourceCoefficientBudget_nonneg
  have hf : ∀ j, j < 65 →
      |(sampledTaylorCoefficient (c:ℝ) (p:ℝ) (fun k => (v k:ℝ)) j).re -
        (ratPanelCoefficient (intSourceCoefficientStream c p v) j:ℝ)| ≤
          (ratSourceCoefficientBudget:ℝ) := by
    intro j hj
    rw [ratPanelCoefficient_stream_eq c p v j hj, abs_sub_comm, ratSourceCoefficientBudget_cast]
    have h := ratSourceRoundedCoefficient_error_budget c p v j hc0 hc1 hp (by omega) hv
    rwa [realSampledTaylorPolynomial_coeff_lt _ _ _ j hj] at h
  have h := panelCoefficientPolynomial_jetNorm_bounds
    (fun j => (sampledTaylorCoefficient (c:ℝ) (p:ℝ) (fun k => (v k:ℝ)) j).re -
      (ratPanelCoefficient (intSourceCoefficientStream c p v) j:ℝ))
    (ratSourceCoefficientBudget:ℝ) hδ hf
  rw [← sampledPolynomial_sub_realPanel] at h
  simpa only [Polynomial.derivative_sub] using h

theorem coefficientNorm_erase_le_add_of_sub (p a : Polynomial ℝ) (d : ℝ)
    (h : coefficientNorm (p-a) ≤ d) :
    coefficientNorm (p.erase 0) ≤ coefficientNorm (a.erase 0)+d := by
  have he : p.erase 0-a.erase 0 = (p-a).erase 0 := by
    ext j
    by_cases hj : j=0 <;> simp [Polynomial.coeff_erase, hj]
  apply coefficientNorm_le_of_sub
  rw [he]
  exact (coefficientNorm_erase_zero_le (p-a)).trans h

def ratPanelD0 : ℚ := 65*ratSourceCoefficientBudget
def ratPanelD1 : ℚ := 65*(ratSourceCoefficientBudget*64)
def ratPanelD2 : ℚ := 65*(ratSourceCoefficientBudget*64*63)

def ratPanelCurvaturePerturbation (a : List ℤ) : ℚ :=
  let p := ratPanelPolynomial a
  ratPanelD1*(2*ratCoefficientNorm p.derivative+ratPanelD1)+
    ratPanelD0*(ratCoefficientNorm p.derivative.derivative+ratPanelD2)+
    ratCoefficientNorm p*ratPanelD2

def ratPanelCurvatureErrorUpper (a : List ℤ) : ℚ :=
  let p := ratPanelPolynomial a
  ratSourcePanelJetUpper*(2*(ratCoefficientNorm p.derivative+ratPanelD1)+
    (ratCoefficientNorm p+ratPanelD0)+(ratCoefficientNorm p.derivative.derivative+ratPanelD2))+
    2*ratSourcePanelJetUpper^2

def ratRecordedConstantLower (i : Fin 318) : ℚ :=
  ((recordedMarginAt i).q0:ℚ)/(10:ℚ)^(recordedMarginAt i).scale
def ratRecordedOffUpper (i : Fin 318) : ℚ :=
  ((recordedMarginAt i).off:ℚ)/(10:ℚ)^(recordedMarginAt i).scale
def ratRecordedErrorUpper (i : Fin 318) : ℚ :=
  ((recordedMarginAt i).err:ℚ)/(10:ℚ)^(recordedMarginAt i).scale

def SourcePanelChecks (i : Fin 318) (a : List ℤ) : Prop :=
  a.length=65 ∧
  ratRecordedConstantLower i ≤ (ratCurvaturePolynomial (ratPanelPolynomial a)).coeff 0 -
    ratPanelCurvaturePerturbation a ∧
  ratCoefficientNorm ((ratCurvaturePolynomial (ratPanelPolynomial a)).erase 0)+
    ratPanelCurvaturePerturbation a ≤ ratRecordedOffUpper i ∧
  ratPanelCurvatureErrorUpper a ≤ ratRecordedErrorUpper i

instance (i : Fin 318) (a : List ℤ) : Decidable (SourcePanelChecks i a) := by
  unfold SourcePanelChecks
  infer_instance

def sourcePanelCheck (i : Fin 318) (a : List ℤ) : Bool := decide (SourcePanelChecks i a)

theorem sourcePanelCheck_iff (i : Fin 318) (a : List ℤ) :
    sourcePanelCheck i a = true ↔ SourcePanelChecks i a := by
  simp [sourcePanelCheck]

def ratSourcePanelCenter (i : Fin 318) : ℚ := (2*(i.val:ℚ)+1)/200

theorem ratSourcePanelCenter_cast (i : Fin 318) :
    (ratSourcePanelCenter i:ℝ) = sourcePanelCenter i := by
  unfold ratSourcePanelCenter sourcePanelCenter
  push_cast
  rfl

theorem ratSourcePanelCenter_bounds (i : Fin 318) :
    0 ≤ ratSourcePanelCenter i ∧ ratSourcePanelCenter i ≤ 40 := by
  have hi : (i.val:ℚ) ≤ 317 := by exact_mod_cast (show i.val ≤ 317 by omega)
  have hi0 : (0:ℚ) ≤ i.val := Nat.cast_nonneg _
  unfold ratSourcePanelCenter
  constructor
  · positivity
  · linarith

theorem ratRecordedBounds_cast (i : Fin 318) :
    (ratRecordedConstantLower i:ℝ)=recordedConstantLower i ∧
    (ratRecordedOffUpper i:ℝ)=recordedOffUpper i ∧
    (ratRecordedErrorUpper i:ℝ)=recordedErrorUpper i := by
  simp [ratRecordedConstantLower, ratRecordedOffUpper, ratRecordedErrorUpper,
    recordedConstantLower, recordedOffUpper, recordedErrorUpper]

theorem approximate_source_samples_abs_bound (v : ℕ → ℚ)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-(v k:ℝ)| ≤ 2/(10:ℝ)^120) :
    ∀ (k : ℕ), k ≤ 13600 → |(v k:ℝ)| ≤ 43046722 := by
  intro k hk
  have hreal : reciprocalTransform ((k:ℝ)/40) =
      ((reciprocalTransform ((k:ℝ)/40)).re:ℂ) :=
    (Complex.conj_eq_iff_re.mp (reciprocalTransform_conj ((k:ℝ)/40))).symm
  apply approximate_sample_abs_le ((k:ℝ)/40) (v k:ℝ) (2/(10:ℝ)^120) (by norm_num)
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hv k hk

theorem ratPanelD_nonneg : 0 ≤ ratPanelD0 ∧ 0 ≤ ratPanelD1 ∧ 0 ≤ ratPanelD2 := by
  have h := ratSourceCoefficientBudget_nonneg
  unfold ratPanelD0 ratPanelD1 ratPanelD2
  exact ⟨by positivity, by positivity, by positivity⟩

theorem ratPanelCurvaturePerturbation_cast (a : List ℤ) :
    (ratPanelCurvaturePerturbation a:ℝ) =
      (ratPanelD1:ℝ)*(2*coefficientNorm (realPanelPolynomial a).derivative+ratPanelD1)+
        (ratPanelD0:ℝ)*(coefficientNorm (realPanelPolynomial a).derivative.derivative+ratPanelD2)+
        coefficientNorm (realPanelPolynomial a)*(ratPanelD2:ℝ) := by
  simp only [ratPanelCurvaturePerturbation, realPanelPolynomial, Polynomial.derivative_map,
    coefficientNorm_map_rat, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

theorem ratPanelCurvatureErrorUpper_cast (a : List ℤ) :
    (ratPanelCurvatureErrorUpper a:ℝ) =
      (ratSourcePanelJetUpper:ℝ)*(2*(coefficientNorm (realPanelPolynomial a).derivative+ratPanelD1)+
        (coefficientNorm (realPanelPolynomial a)+ratPanelD0)+
        (coefficientNorm (realPanelPolynomial a).derivative.derivative+ratPanelD2))+
      2*(ratSourcePanelJetUpper:ℝ)^2 := by
  simp only [ratPanelCurvatureErrorUpper, realPanelPolynomial, Polynomial.derivative_map,
    coefficientNorm_map_rat, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]

theorem ratPanelCurvatureFields_cast (a : List ℤ) :
    (((ratCurvaturePolynomial (ratPanelPolynomial a)).coeff 0:ℚ):ℝ) =
        (curvaturePolynomial (realPanelPolynomial a)).coeff 0 ∧
    (ratCoefficientNorm ((ratCurvaturePolynomial (ratPanelPolynomial a)).erase 0):ℝ) =
        coefficientNorm ((curvaturePolynomial (realPanelPolynomial a)).erase 0) := by
  constructor
  · rw [realPanelPolynomial, curvaturePolynomial_map_rat, Polynomial.coeff_map]
    rfl
  · rw [realPanelPolynomial, curvaturePolynomial_map_rat, erase_zero_map_rat,
      coefficientNorm_map_rat]

theorem sourcePanel_stream_jetNorm_difference (i : Fin 318) (v : ℕ → ℚ)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-(v k:ℝ)| ≤ 2/(10:ℝ)^120) :
    let P := sourcePanelPolynomial (fun k => (v k:ℝ)) i
    let A := realPanelPolynomial (intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v)
    coefficientNorm (P-A) ≤ (ratPanelD0:ℝ) ∧
    coefficientNorm (P.derivative-A.derivative) ≤ (ratPanelD1:ℝ) ∧
    coefficientNorm (P.derivative.derivative-A.derivative.derivative) ≤ (ratPanelD2:ℝ) := by
  have h := sampled_stream_jetNorm_difference (ratSourcePanelCenter i) sourcePiMidpoint v
    (ratSourcePanelCenter_bounds i).1 (ratSourcePanelCenter_bounds i).2
    sourcePiMidpoint_ge_three (approximate_source_samples_abs_bound v hv)
  simpa only [ratSourcePanelCenter_cast, sourcePanelPolynomial, ratPanelD0, ratPanelD1, ratPanelD2,
    Rat.cast_mul, Rat.cast_ofNat] using h

theorem sourcePanelCheck_enclosures (i : Fin 318) (v : ℕ → ℚ)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-(v k:ℝ)| ≤ 2/(10:ℝ)^120)
    (hcheck : sourcePanelCheck i
      (intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v) = true) :
    let P := sourcePanelPolynomial (fun k => (v k:ℝ)) i
    recordedConstantLower i ≤ (curvaturePolynomial P).coeff 0 ∧
    coefficientNorm ((curvaturePolynomial P).erase 0) ≤ recordedOffUpper i ∧
    polynomialCurvatureError P sourcePanelJetError ≤ recordedErrorUpper i := by
  let a := intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v
  let P := sourcePanelPolynomial (fun k => (v k:ℝ)) i
  let A := realPanelPolynomial a
  have hc : SourcePanelChecks i a := (sourcePanelCheck_iff i a).mp hcheck
  have hN := sourcePanel_stream_jetNorm_difference i v hv
  change coefficientNorm (P-A) ≤ (ratPanelD0:ℝ) ∧
    coefficientNorm (P.derivative-A.derivative) ≤ (ratPanelD1:ℝ) ∧
    coefficientNorm (P.derivative.derivative-A.derivative.derivative) ≤ (ratPanelD2:ℝ) at hN
  have hd0 : (0:ℝ) ≤ ratPanelD0 := (Rat.cast_nonneg (K := ℝ)).mpr ratPanelD_nonneg.1
  have hd1 : (0:ℝ) ≤ ratPanelD1 := (Rat.cast_nonneg (K := ℝ)).mpr ratPanelD_nonneg.2.1
  have hd2 : (0:ℝ) ≤ ratPanelD2 := (Rat.cast_nonneg (K := ℝ)).mpr ratPanelD_nonneg.2.2
  have hD : coefficientNorm (curvaturePolynomial P-curvaturePolynomial A) ≤
      (ratPanelCurvaturePerturbation a:ℝ) := by
    rw [ratPanelCurvaturePerturbation_cast]
    exact curvaturePolynomial_coefficientNorm_difference P A ratPanelD0 ratPanelD1 ratPanelD2
      hd0 hd1 hd2 hN.1 hN.2.1 hN.2.2
  have hq := (Rat.cast_le (K := ℝ)).mpr hc.2.1
  have ho := (Rat.cast_le (K := ℝ)).mpr hc.2.2.1
  have he := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2
  simp only [Rat.cast_sub, (ratRecordedBounds_cast i).1, (ratPanelCurvatureFields_cast a).1] at hq
  simp only [Rat.cast_add, (ratRecordedBounds_cast i).2.1, (ratPanelCurvatureFields_cast a).2] at ho
  simp only [(ratRecordedBounds_cast i).2.2] at he
  change recordedConstantLower i ≤ (curvaturePolynomial P).coeff 0 ∧
    coefficientNorm ((curvaturePolynomial P).erase 0) ≤ recordedOffUpper i ∧
    polynomialCurvatureError P sourcePanelJetError ≤ recordedErrorUpper i
  refine ⟨?_, ?_, ?_⟩
  · have h := (abs_coeff_le_coefficientNorm (curvaturePolynomial P-curvaturePolynomial A) 0).trans hD
    rw [Polynomial.coeff_sub] at h
    have hl := (abs_le.mp h).1
    dsimp only [A] at hl
    linarith
  · exact (coefficientNorm_erase_le_add_of_sub (curvaturePolynomial P)
      (curvaturePolynomial A) (ratPanelCurvaturePerturbation a:ℝ) hD).trans ho
  · apply le_trans _ he
    rw [ratPanelCurvatureErrorUpper_cast]
    have hn0 := coefficientNorm_le_of_sub P A ratPanelD0 hN.1
    have hn1 := coefficientNorm_le_of_sub P.derivative A.derivative ratPanelD1 hN.2.1
    have hn2 := coefficientNorm_le_of_sub P.derivative.derivative A.derivative.derivative ratPanelD2 hN.2.2
    have hsum : 2*coefficientNorm P.derivative+coefficientNorm P+coefficientNorm P.derivative.derivative ≤
        2*(coefficientNorm A.derivative+ratPanelD1)+(coefficientNorm A+ratPanelD0)+
          (coefficientNorm A.derivative.derivative+ratPanelD2) := by linarith
    have hE := sourcePanelJetError_le_ratUpper
    have he0 : (0:ℝ) ≤ ratSourcePanelJetUpper := (Rat.cast_nonneg (K := ℝ)).mpr ratSourcePanelJetUpper_nonneg
    have hsum0 : 0 ≤ 2*coefficientNorm P.derivative+coefficientNorm P+
        coefficientNorm P.derivative.derivative := by
      have h0 := coefficientNorm_nonneg P
      have h1 := coefficientNorm_nonneg P.derivative
      have h2 := coefficientNorm_nonneg P.derivative.derivative
      linarith
    have hprod := mul_le_mul hE hsum hsum0 he0
    have hsq := mul_le_mul hE hE sourcePanelJetError_nonneg he0
    unfold polynomialCurvatureError
    simpa only [pow_two] using add_le_add hprod (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 2))

theorem sourcePanelCheck_density_curvature_pos (i : Fin 318) (v : ℕ → ℚ)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-(v k:ℝ)| ≤ 2/(10:ℝ)^120)
    (hcheck : sourcePanelCheck i
      (intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v) = true)
    (x : ℝ) (hx : |panelCoordinate i.val x| ≤ 1) :
    0 < curvatureJet (density x) (deriv density x) (deriv (deriv density) x) := by
  have h := sourcePanelCheck_enclosures i v hv hcheck
  have hd := sourcePanelPolynomial_derivative_errors (fun k => (v k:ℝ)) hv i x hx
  exact curvatureJet_positive_of_scaled _ _ _ (1/200)
    (curvature_positive_of_enclosed_panel (sourcePanelPolynomial (fun k => (v k:ℝ)) i)
      (panelCoordinate i.val x) (density x) ((1/200)*deriv density x)
      ((1/200:ℝ)^2*deriv (deriv density) x) sourcePanelJetError
      (recordedConstantLower i) (recordedOffUpper i) (recordedErrorUpper i)
      hx sourcePanelJetError_nonneg hd.1 hd.2.1 hd.2.2 h.1 h.2.1 h.2.2 (recorded_bounds_strict_margin i))

def densityCompactEnclosures_of_stream_checks (v : ℕ → ℚ)
    (hv : ∀ (k : ℕ), k ≤ 13600 → |(reciprocalTransform ((k:ℝ)/40)).re-(v k:ℝ)| ≤ 2/(10:ℝ)^120)
    (hchecks : ∀ i, sourcePanelCheck i
      (intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v) = true) :
    DensityCompactEnclosures :=
  densityCompactEnclosures_of_source_coefficients (fun k => (v k:ℝ)) hv
    (fun i => (sourcePanelCheck_enclosures i v hv (hchecks i)).1)
    (fun i => (sourcePanelCheck_enclosures i v hv (hchecks i)).2.1)
    (fun i => (sourcePanelCheck_enclosures i v hv (hchecks i)).2.2)

end ReciprocalXi

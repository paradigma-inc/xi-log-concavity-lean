import ProofWorkspace.Final.XiJensenFull
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Real
namespace ReciprocalXi

theorem xiGrowth_log_le (n : ℕ) :
    Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) ≤
      ((n:ℝ)+2)*Real.log ((n:ℝ)+2) := by
  have hf : (n.factorial:ℝ) ≤ ((n:ℝ)+2)^n := by
    have hn : (n.factorial:ℝ) ≤ (n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    exact hn.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) n)
  have hb : ((n:ℝ)+2)^2*(n.factorial:ℝ) ≤ ((n:ℝ)+2)^(n+2) := by
    calc
      _ ≤ ((n:ℝ)+2)^2*((n:ℝ)+2)^n := mul_le_mul_of_nonneg_left hf (sq_nonneg _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hp : (0:ℝ) < ((n:ℝ)+2)^2*(n.factorial:ℝ) := by positivity
  have h := Real.log_le_log hp hb
  simpa only [Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using h

def F_zeroCountConstant : ℝ := |Real.log ‖F 0‖| / Real.log 2

theorem F_zeroCountConstant_nonneg : 0 ≤ F_zeroCountConstant := by
  exact div_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))

theorem F_zeroCount_dyadic (k : ℕ) :
    (F_zeroCount ((2:ℝ)^k) : ℝ) ≤
      4*(2:ℝ)^k*((k:ℝ)+2)+F_zeroCountConstant := by
  have hp : (0:ℝ) < 2^k := by positivity
  have hp1 : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hl : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := F_zeroCount_log_two_le (2*(2:ℝ)^k) (2^k+1)
    (by positivity) (by norm_num; linarith)
  have hg := xiGrowth_log_le (2^k+1)
  norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h hg
  have heq : 2*(2:ℝ)^k/2 = 2^k := by ring
  rw [heq] at h
  have hb : (2:ℝ)^k+1+2 ≤ (2:ℝ)^(k+2) := by
    rw [pow_add]
    norm_num
    linarith
  have hlog : Real.log ((2:ℝ)^k+1+2) ≤ ((k:ℝ)+2)*Real.log 2 := by
    have ht := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^k+1+2) hb
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using ht
  have hg' : ((2:ℝ)^k+1+2)*Real.log ((2:ℝ)^k+1+2) ≤
      (4*(2:ℝ)^k)*(((k:ℝ)+2)*Real.log 2) := by
    have hb' : (2:ℝ)^k+1+2 ≤ 4*(2:ℝ)^k := by linarith
    exact mul_le_mul hb' hlog (Real.log_nonneg (by linarith)) (by positivity)
  have hc : F_zeroCountConstant*Real.log 2 = |Real.log ‖F 0‖| := by
    exact div_mul_cancel₀ _ (ne_of_gt hl)
  have ha : -Real.log ‖F 0‖ ≤ |Real.log ‖F 0‖| := neg_le_abs _
  apply (mul_le_mul_iff_left₀ hl).mp
  calc
    _ = (F_zeroCount ((2:ℝ)^k) : ℝ)*Real.log 2 := by ring
    _ ≤ Real.log (((2:ℝ)^k+1+2)^2*((2^k+1).factorial:ℝ)) - Real.log ‖F 0‖ := h
    _ ≤ (4*(2:ℝ)^k)*(((k:ℝ)+2)*Real.log 2)+|Real.log ‖F 0‖| := by
      linarith only [hg, hg', ha]
    _ = _ := by rw [← hc]; ring

def F_zeroShellBound (k : ℕ) : ℝ :=
  8*((k:ℝ)+3)*(1/2:ℝ)^k+F_zeroCountConstant*(1/4:ℝ)^k

theorem F_zeroShellBound_nonneg (k : ℕ) : 0 ≤ F_zeroShellBound k := by
  unfold F_zeroShellBound
  positivity [F_zeroCountConstant_nonneg]

theorem F_zeroShellBound_eq (k : ℕ) :
    F_zeroShellBound k =
      (4*(2:ℝ)^(k+1)*((k:ℝ)+3)+F_zeroCountConstant) / ((2:ℝ)^k)^2 := by
  have hp : (2:ℝ)^k ≠ 0 := by positivity
  have hfour : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
    calc
      _ = ((2:ℝ)^2)^k := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; omega
  simp only [F_zeroShellBound, one_div_pow, hfour, pow_succ]
  field_simp
  ring

theorem summable_F_zeroShellBound : Summable F_zeroShellBound := by
  have h1 : Summable (fun k : ℕ ↦ (k:ℝ)*(1/2:ℝ)^k) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖<1))
  have h2 : Summable (fun k : ℕ ↦ (1/2:ℝ)^k) := summable_geometric_of_norm_lt_one (by norm_num)
  have h4 : Summable (fun k : ℕ ↦ (1/4:ℝ)^k) := summable_geometric_of_norm_lt_one (by norm_num)
  have h := ((h1.add (h2.mul_left 3)).mul_left 8).add (h4.mul_left F_zeroCountConstant)
  exact h.congr (fun k ↦ by simp only [F_zeroShellBound]; ring)

theorem F_finite_shell_sum_le (k : ℕ) (s : Finset ℂ)
    (hs : ∀ z ∈ s, F z = 0 ∧ (2:ℝ)^k ≤ ‖z‖ ∧ ‖z‖ < (2:ℝ)^(k+1)) :
    (∑ z ∈ s, (analyticOrderNatAt F z : ℝ)/‖z‖^2) ≤ F_zeroShellBound k := by
  classical
  have hp : (0:ℝ) < (2^k)^2 := by positivity
  have hsub : s ⊆ F_zeroFinset ((2:ℝ)^(k+1)) := by
    intro z hz
    exact (mem_F_zeroFinset _ z).mpr ⟨(hs z hz).1,(hs z hz).2.2.le⟩
  have hsum : (∑ z ∈ s, (analyticOrderNatAt F z : ℝ)) ≤
      (F_zeroCount ((2:ℝ)^(k+1)) : ℝ) := by
    simp only [F_zeroCount, Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.cast_nonneg _)
  calc
    _ ≤ ∑ z ∈ s, (analyticOrderNatAt F z : ℝ)/((2:ℝ)^k)^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp
        (pow_le_pow_left₀ (by positivity) (hs z hz).2.1 2)
    _ = (∑ z ∈ s, (analyticOrderNatAt F z : ℝ))/((2:ℝ)^k)^2 := by rw [Finset.sum_div]
    _ ≤ (F_zeroCount ((2:ℝ)^(k+1)) : ℝ)/((2:ℝ)^k)^2 :=
      div_le_div_of_nonneg_right hsum hp.le
    _ ≤ (4*(2:ℝ)^(k+1)*((k:ℝ)+3)+F_zeroCountConstant)/((2:ℝ)^k)^2 := by
      apply div_le_div_of_nonneg_right _ hp.le
      convert F_zeroCount_dyadic (k+1) using 1
      push_cast
      ring
    _ = F_zeroShellBound k := (F_zeroShellBound_eq k).symm

abbrev FZero := {z : ℂ // F z = 0}

def F_zeroShellIndex (z : FZero) : ℕ := Classical.choose
  (exists_nat_pow_near (F_zero_norm_gt_one z.val z.property).le (by norm_num : (1:ℝ)<2))

theorem F_zeroShellIndex_spec (z : FZero) :
    (2:ℝ)^(F_zeroShellIndex z) ≤ ‖z.val‖ ∧
      ‖z.val‖ < (2:ℝ)^(F_zeroShellIndex z+1) := Classical.choose_spec
  (exists_nat_pow_near (F_zero_norm_gt_one z.val z.property).le (by norm_num : (1:ℝ)<2))

theorem summable_F_zero_order_div_norm_sq :
    Summable (fun z : FZero ↦ (analyticOrderNatAt F z.val : ℝ)/‖z.val‖^2) := by
  classical
  apply summable_of_sum_le (c := ∑' k, F_zeroShellBound k) (fun z ↦ by positivity)
  intro s
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image F_zeroShellIndex)
    (fun z hz ↦ Finset.mem_image_of_mem F_zeroShellIndex hz)
    (fun z : FZero ↦ (analyticOrderNatAt F z.val : ℝ)/‖z.val‖^2)
  rw [← hgroup]
  apply le_trans _ (summable_F_zeroShellBound.sum_le_tsum (s.image F_zeroShellIndex)
    (fun k _ ↦ F_zeroShellBound_nonneg k))
  apply Finset.sum_le_sum
  intro k hk
  let t := s.filter (fun z ↦ F_zeroShellIndex z = k)
  have hshell : ∀ z ∈ t.image Subtype.val,
      F z = 0 ∧ (2:ℝ)^k ≤ ‖z‖ ∧ ‖z‖ < (2:ℝ)^(k+1) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have hwk : F_zeroShellIndex w = k := (Finset.mem_filter.mp hw).2
    exact ⟨w.property, by simpa only [hwk] using F_zeroShellIndex_spec w⟩
  have hb := F_finite_shell_sum_le k (t.image Subtype.val) hshell
  rw [Finset.sum_image (fun a _ b _ h ↦ Subtype.ext h)] at hb
  exact hb

theorem summable_F_zero_inv_norm_sq :
    Summable (fun z : FZero ↦ (‖z.val‖^2)⁻¹) := by
  apply Summable.of_nonneg_of_le (fun z ↦ by positivity) _ summable_F_zero_order_div_norm_sq
  intro z
  have ho : (1:ℝ) ≤ analyticOrderNatAt F z.val := by
    exact_mod_cast F_zero_order_pos z.val z.property
  simpa only [one_div] using div_le_div_of_nonneg_right ho (sq_nonneg ‖z.val‖)

end ReciprocalXi


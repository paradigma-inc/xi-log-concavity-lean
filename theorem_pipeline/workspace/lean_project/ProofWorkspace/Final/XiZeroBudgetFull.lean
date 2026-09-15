import ProofWorkspace.Final.XiPairedProductFull
import ProofWorkspace.Final.XiStripBoundsFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace ReciprocalXi

theorem F_zero_norm_bounds : (1:ℝ)/16 ≤ ‖F 0‖ ∧ ‖F 0‖ ≤ 1 := by
  have hlo := (xi_re_ge_wide_rectangle (1/2) (by norm_num) (by norm_num)
    (by norm_num)).trans (Complex.re_le_norm _)
  have hhi := xi_norm_le_real_wide (1/2) (by norm_num) (by norm_num)
  have he : ‖F 0‖ = ‖xi (1/2)‖/4 := by simp [F, norm_div]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hhi
  rw [he]
  constructor <;> linarith

theorem F_zeroCountConstant_le_four : F_zeroCountConstant ≤ 4 := by
  have hp : 0 < ‖F 0‖ := norm_pos_iff.mpr F_zero_ne_zero
  have hl : Real.log ‖F 0‖ ≤ 0 := Real.log_nonpos hp.le F_zero_norm_bounds.2
  have hb := Real.log_le_log (by norm_num : (0:ℝ)<1/16) F_zero_norm_bounds.1
  have he : Real.log ((1:ℝ)/16) = -4*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have h16 : (16:ℝ)=2^4 := by norm_num
    rw [h16, Real.log_pow]
    ring
  rw [he] at hb
  unfold F_zeroCountConstant
  rw [abs_of_nonpos hl]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  linarith

theorem F_zeroShellBound_tsum : (∑' k : ℕ, F_zeroShellBound k) =
    64+4*F_zeroCountConstant/3 := by
  have h1 : HasSum (fun k : ℕ ↦ (k:ℝ)*(1/2:ℝ)^k) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1) using 1
    norm_num
  have h2 : HasSum (fun k : ℕ ↦ (1/2:ℝ)^k) 2 := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1) using 1
    norm_num
  have h4 : HasSum (fun k : ℕ ↦ (1/4:ℝ)^k) (4/3) := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖<1) using 1
    norm_num
  have hh := ((h1.add (h2.mul_left 3)).mul_left 8).add (h4.mul_left F_zeroCountConstant)
  have he : (fun k : ℕ ↦ 8*((k:ℝ)*(1/2:ℝ)^k+3*(1/2:ℝ)^k)+
      F_zeroCountConstant*(1/4:ℝ)^k) = F_zeroShellBound := by
    funext k
    unfold F_zeroShellBound
    ring
  rw [he] at hh
  convert hh.tsum_eq using 1
  ring

theorem F_zero_order_inv_norm_sq_tsum_le :
    (∑' z : FZero, (analyticOrderNatAt F z.val:ℝ)/‖z.val‖^2) ≤
      ∑' k : ℕ, F_zeroShellBound k := by
  classical
  apply summable_F_zero_order_div_norm_sq.tsum_le_of_sum_le
  intro s
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s:=s) (t:=s.image F_zeroShellIndex)
    (fun z hz ↦ Finset.mem_image_of_mem F_zeroShellIndex hz)
    (fun z : FZero ↦ (analyticOrderNatAt F z.val:ℝ)/‖z.val‖^2)
  rw [← hgroup]
  apply le_trans _ (summable_F_zeroShellBound.sum_le_tsum (s.image F_zeroShellIndex)
    (fun k _ ↦ F_zeroShellBound_nonneg k))
  apply Finset.sum_le_sum
  intro k hk
  let t := s.filter (fun z ↦ F_zeroShellIndex z=k)
  have hshell : ∀ z∈t.image Subtype.val,
      F z=0 ∧ (2:ℝ)^k≤‖z‖ ∧ ‖z‖<(2:ℝ)^(k+1) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have hwk : F_zeroShellIndex w=k := (Finset.mem_filter.mp hw).2
    exact ⟨w.property, by simpa only [hwk] using F_zeroShellIndex_spec w⟩
  have hb := F_finite_shell_sum_le k (t.image Subtype.val) hshell
  rw [Finset.sum_image (fun a _ b _ h ↦ Subtype.ext h)] at hb
  exact hb

theorem F_zeroOccurrence_inv_norm_sq_tsum_le_seventy :
    (∑' z : FZeroOccurrence, (‖z.1.val‖^2)⁻¹) ≤ 70 := by
  rw [summable_F_zeroOccurrence_inv_norm_sq.tsum_sigma]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← div_eq_mul_inv]
  have h := F_zero_order_inv_norm_sq_tsum_le
  rw [F_zeroShellBound_tsum] at h
  linarith [F_zeroCountConstant_le_four]

theorem F_pairRoot_inv_norm_sq_tsum_le_seventy :
    (∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹) ≤ 70 := by
  apply le_trans _ F_zeroOccurrence_inv_norm_sq_tsum_le_seventy
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
    summable_F_pairRoot_inv_norm_sq summable_F_zeroOccurrence_inv_norm_sq

end ReciprocalXi


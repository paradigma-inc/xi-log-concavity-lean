import ProofWorkspace.Final.XiStripBoundsFull
import ProofWorkspace.Final.XiZeroGeometryFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
open Complex
namespace ReciprocalXi

theorem exp_three_ge_twenty : (20:ℝ)≤Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤3) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem thetaMellin_bound_le_one_fifteen :
    4*Real.exp (-Real.pi)/Real.pi≤(1:ℝ)/15 := by
  have he : (20:ℝ)≤Real.exp Real.pi := exp_three_ge_twenty.trans
    (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have hi : Real.exp (-Real.pi)≤(1:ℝ)/20 := by
    rw [Real.exp_neg,← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  calc
    _≤(4*(1/20:ℝ))/Real.pi := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi (by norm_num)) Real.pi_pos.le
    _≤(4*(1/20:ℝ))/3 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) Real.pi_gt_three.le
    _=_ := by norm_num

theorem F_zero_abs_re_gt_seven (z : ℂ) (hz : F z=0) : 7 < |z.re| := by
  by_contra h
  have hx : |z.re|≤7 := le_of_not_gt h
  have hy := abs_lt.mp (F_zero_im_bound z hz)
  let s : ℂ := 1/2+I*z/2
  have hre : s.re=(1-z.im)/2 := by simp [s,Complex.mul_re]; ring
  have him : s.im=z.re/2 := by simp [s,Complex.mul_im]
  have hsr0 : 0≤s.re := by rw [hre]; linarith
  have hsr1 : s.re≤1 := by rw [hre]; linarith
  have hsr2 : s.re^2≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hsr0 hsr1 2
  have htr2 : (s.re-1)^2≤1 := by
    have hh := pow_le_pow_left₀ (show 0≤1-s.re by linarith)
      (show 1-s.re≤1 by linarith) 2
    norm_num at hh
    nlinarith
  have hsi2 : s.im^2≤49/4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg z.re) hx 2
    rw [sq_abs] at hh
    rw [him]
    nlinarith
  have hn1 : ‖s‖^2≤53/4 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith
  have hn2 : ‖s-1‖^2≤53/4 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero]
    nlinarith
  have hp : ‖s‖*‖s-1‖≤53/4 := by nlinarith [sq_nonneg (‖s‖-‖s-1‖)]
  have hc : ‖completedRiemannZeta₀ s‖≤(1:ℝ)/15 :=
    (completedRiemannZeta₀_norm_le_thetaBound_wide s (by linarith)
      (by linarith)).trans thetaMellin_bound_le_one_fifteen
  have hb : ‖s*(s-1)*completedRiemannZeta₀ s‖≤(53/4:ℝ)*(1/15) := by
    rw [norm_mul,norm_mul]
    exact mul_le_mul hp hc (norm_nonneg _) (by norm_num)
  change ((s*(s-1)*completedRiemannZeta₀ s+1)/2)/4=0 at hz
  have hz' : s*(s-1)*completedRiemannZeta₀ s+1=0 := by
    have he := congrArg (fun w : ℂ ↦ w*8) hz
    convert he using 1 <;> ring
  have hneg : s*(s-1)*completedRiemannZeta₀ s=(-1:ℂ) := by
    linear_combination hz'
  rw [hneg] at hb
  norm_num at hb

theorem complex_unit_power_sub_one_norm_le (u : ℂ) (hu : ‖u‖=1) (n : ℕ) :
    ‖u^n-1‖≤(n:ℝ)*‖u-1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : u^(n+1)-1=u*(u^n-1)+(u-1) := by ring
    rw [he]
    calc
      _≤‖u*(u^n-1)‖+‖u-1‖ := norm_add_le _ _
      _≤(n:ℝ)*‖u-1‖+‖u-1‖ := by
        rw [norm_mul,hu,one_mul]
        linarith
      _=_ := by push_cast; ring

theorem complex_unit_power_re_lower (u : ℂ) (hu : ‖u‖=1) (n : ℕ) :
    1-(n:ℝ)^2*(1-u.re)≤(u^n).re := by
  have hnorm (w : ℂ) (hw : ‖w‖=1) : ‖w-1‖^2=2*(1-w.re) := by
    rw [Complex.sq_norm,Complex.normSq_sub]
    have hh : Complex.normSq w=1 := by rw [← Complex.sq_norm,hw]; norm_num
    simp [hh]
    <;> ring
  have hn : ‖u^n‖=1 := by rw [norm_pow,hu,one_pow]
  have hh := pow_le_pow_left₀ (norm_nonneg (u^n-1))
    (complex_unit_power_sub_one_norm_le u hu n) 2
  rw [mul_pow,hnorm u hu,hnorm (u^n) hn] at hh
  nlinarith

theorem complex_normalized_re_deficit (a : ℂ) (ha : 0<a.re) (hi : |a.im|≤1) :
    1-a.re/‖a‖≤1/(2*a.re^2) := by
  have hr : 0<‖a‖ := ha.trans_le (Complex.re_le_norm a)
  have har : a.re≤‖a‖ := Complex.re_le_norm a
  have hi2 : a.im^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hi
  have hs : ‖a‖^2≤a.re^2+1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith
  have hp : (‖a‖-a.re)*(‖a‖+a.re)≤1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hp ha.le
  have he : (‖a‖-a.re)*(2*a.re^2)≤‖a‖ := by
    nlinarith [mul_nonneg ha.le (sq_nonneg (‖a‖-a.re))]
  calc
    _=(‖a‖-a.re)/‖a‖ := by field_simp <;> ring
    _≤_ := (div_le_div_iff₀ hr (by positivity : (0:ℝ)<2*a.re^2)).mpr (by simpa using he)

theorem complex_inverse_power_re_lower (a : ℂ) (ha : 0<a.re)
    (hi : |a.im|≤1) (n : ℕ) :
    (1-(n:ℝ)^2/(2*a.re^2))/‖a‖^n≤((a⁻¹)^n).re := by
  have hr : 0<‖a‖ := ha.trans_le (Complex.re_le_norm a)
  let u : ℂ := a/(‖a‖:ℂ)
  have hu : ‖u‖=1 := by
    dsimp [u]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,div_self hr.ne']
  have hure : u.re=a.re/‖a‖ := by simp only [u,Complex.div_ofReal_re]
  have hpow := complex_unit_power_re_lower u hu n
  have hdef := mul_le_mul_of_nonneg_left (complex_normalized_re_deficit a ha hi)
    (sq_nonneg (n:ℝ))
  rw [hure] at hpow
  have hb : 1-(n:ℝ)^2/(2*a.re^2)≤(u^n).re := by
    rw [mul_one_div] at hdef
    linarith
  have hup : (u^n).re=(a^n).re/‖a‖^n := by
    dsimp [u]
    rw [div_pow,← Complex.ofReal_pow,Complex.div_ofReal_re]
  have he : ((a^n)⁻¹).re=(u^n).re/‖a‖^n := by
    rw [Complex.inv_re,← Complex.sq_norm,norm_pow,hup]
    field_simp [pow_ne_zero n hr.ne']
    <;> ring
  rw [inv_pow,he]
  exact div_le_div_of_nonneg_right hb (pow_nonneg hr.le n)

end ReciprocalXi


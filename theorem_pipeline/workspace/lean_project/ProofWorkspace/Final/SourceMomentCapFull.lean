import ProofWorkspace.Final.SpecialSourceSamplesFull
import ProofWorkspace.Final.XiZeroSymmetryFull

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace ReciprocalXi

theorem F_real_eq_ofReal_re (x : ℝ) : F (x:ℂ)=((F (x:ℂ)).re:ℂ) := by
  have h := F_conj (x:ℂ)
  rw [Complex.conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

theorem F_zero_re_source_upper :
    0≤(F 0).re ∧ (F 0).re≤124280194548/(10:ℝ)^12 := by
  have hlo : (0:ℚ)≤candidateXiZeroValues.1 := by decide +kernel
  have hup : candidateXiZeroValues.2≤4*124280194548/(10:ℚ)^12 := by decide +kernel
  have hlo' : (0:ℝ)≤(candidateXiZeroValues.1:ℝ) := by exact_mod_cast hlo
  have hup' : (candidateXiZeroValues.2:ℝ)≤((4*124280194548/(10:ℚ)^12:ℚ):ℝ) := Rat.cast_le.mpr hup
  push_cast at hup'
  have h := xiCentral_certified_candidate_enclosure
  have he : (F 0).re=(xi (1/2)).re/4 := by norm_num [F, Complex.div_re]
  rw [he]
  constructor <;> linarith [h.1,h.2]

theorem source_moment_cap_of_F48_lower {a b : ℝ}
    (ha : 2826945028346/(10:ℝ)^11≤a)
    (hb : 4204407927754/(10:ℝ)^11≤b)
    (haR : a<48) (hbR : b<48)
    (h48 : 529169286414/(10:ℝ)^18≤(F (48:ℂ)).re) :
    2*(F 0*((1-(48:ℂ)^2/(a:ℂ)^2)*(1-(48:ℂ)^2/(b:ℂ)^2))/F (48:ℂ)).re≤268341 := by
  have ha0 : 0<a := by norm_num at ha; linarith
  have hb0 : 0<b := by norm_num at hb; linarith
  have h48pos : 0<(F (48:ℂ)).re := by norm_num at h48; linarith
  have hf0 := F_zero_re_source_upper.1
  have hcast : F 0*((1-(48:ℂ)^2/(a:ℂ)^2)*(1-(48:ℂ)^2/(b:ℂ)^2))/F (48:ℂ)=
      ((F 0).re*((48^2/a^2-1)*(48^2/b^2-1))/(F (48:ℂ)).re:ℝ) := by
    have hzero := F_real_eq_ofReal_re 0
    have hfortyeight := F_real_eq_ofReal_re 48
    norm_num only [Complex.ofReal_zero, Complex.ofReal_ofNat] at hzero hfortyeight
    rw [hzero, hfortyeight]
    push_cast
    simp only [Complex.ofReal_re]
    ring
  rw [hcast, Complex.ofReal_re]
  have hap : 0≤48^2/a^2-1 := by
    have he : (1:ℝ)≤48^2/a^2 := (le_div_iff₀ (sq_pos_of_pos ha0)).mpr (by nlinarith)
    linarith
  have hbp : 0≤48^2/b^2-1 := by
    have he : (1:ℝ)≤48^2/b^2 := (le_div_iff₀ (sq_pos_of_pos hb0)).mpr (by nlinarith)
    linarith
  have hau : 48^2/a^2-1≤48^2/(2826945028346/(10:ℝ)^11)^2-1 := by
    gcongr
  have hbu : 48^2/b^2-1≤48^2/(4204407927754/(10:ℝ)^11)^2-1 := by
    gcongr
  have hn : (F 0).re*((48^2/a^2-1)*(48^2/b^2-1))≤
      (124280194548/(10:ℝ)^12)*
        ((48^2/(2826945028346/(10:ℝ)^11)^2-1)*(48^2/(4204407927754/(10:ℝ)^11)^2-1)) := by
    exact mul_le_mul F_zero_re_source_upper.2 (mul_le_mul hau hbu hbp (hap.trans hau))
      (mul_nonneg hap hbp) (by norm_num)
  have hu : (F 0).re*((48^2/a^2-1)*(48^2/b^2-1))/(F (48:ℂ)).re≤
      ((124280194548/(10:ℝ)^12)*
        ((48^2/(2826945028346/(10:ℝ)^11)^2-1)*(48^2/(4204407927754/(10:ℝ)^11)^2-1)))/
          (529169286414/(10:ℝ)^18) := by
    apply div_le_div₀ (by positivity) hn (by norm_num) h48
  norm_num at hu
  linarith

end ReciprocalXi

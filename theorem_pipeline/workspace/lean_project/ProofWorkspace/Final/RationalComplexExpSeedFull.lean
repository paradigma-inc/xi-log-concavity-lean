import ProofWorkspace.Final.RationalComplexFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem ratComplexValue_distance_le (a b : ℚ × ℚ) :
    ‖ratComplexValue a-ratComplexValue b‖≤((|a.1-b.1|+|a.2-b.2|:ℚ):ℝ) := by
  simpa only [Complex.sub_re, Complex.sub_im, ratComplexValue_re, ratComplexValue_im,
    Rat.cast_add, Rat.cast_abs, Rat.cast_sub] using
    Complex.norm_le_abs_re_add_abs_im (ratComplexValue a-ratComplexValue b)

def ratComplexExpSeedValid (u : ℚ × ℚ) (w : ℕ → ℚ × ℚ) : Prop :=
  u.1≤0 ∧
  (ratComplexDivNat u 1024).1^2+(ratComplexDivNat u 1024).2^2≤1 ∧
  (|(w 0).1-(ratComplexExpTaylorScan (ratComplexDivNat u 1024) 40).1| +
    |(w 0).2-(ratComplexExpTaylorScan (ratComplexDivNat u 1024) 40).2| ≤2/(10:ℚ)^60) ∧
  (∀ j : Fin 10, (w j).1^2+(w j).2^2≤1) ∧
  (∀ j : Fin 10,
    |(w ((j:ℕ)+1)).1-(ratComplexMul (w j) (w j)).1| +
    |(w ((j:ℕ)+1)).2-(ratComplexMul (w j) (w j)).2| ≤2/(10:ℚ)^60)

theorem ratComplexExpSeedValid_error (u : ℚ × ℚ) (w : ℕ → ℚ × ℚ)
    (h : ratComplexExpSeedValid u w) :
    ‖ratComplexValue (w 10)-Complex.exp (ratComplexValue u)‖≤1/(10:ℝ)^43 := by
  obtain ⟨hu,hun,hs,hw,hr⟩ := h
  have hre : (ratComplexValue u).re≤0 := by rw [ratComplexValue_re]; exact_mod_cast hu
  have hnorm : ‖ratComplexValue u/1024‖≤1 := by
    have hn := ratComplexValue_norm_le_one _ hun
    rw [ratComplexValue_divNat] at hn
    simpa only [Nat.cast_ofNat] using hn
  have hseed : ‖ratComplexValue (w 0)-complexExpTaylor40 (ratComplexValue u/1024)‖≤2/(10:ℝ)^60 := by
    have hd := ratComplexValue_distance_le (w 0)
      (ratComplexExpTaylorScan (ratComplexDivNat u 1024) 40)
    rw [ratComplexExpTaylorScan_value, ratComplexValue_divNat] at hd
    apply hd.trans
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr hs
  have hstate : ∀ j, j<10 → ‖ratComplexValue (w j)‖≤1 :=
    fun j hj ↦ ratComplexValue_norm_le_one _ (hw ⟨j,hj⟩)
  have hstep : ∀ j, j<10 → ‖ratComplexValue (w (j+1))-(ratComplexValue (w j))^2‖≤2/(10:ℝ)^60 := by
    intro j hj
    have hd := ratComplexValue_distance_le (w (j+1)) (ratComplexMul (w j) (w j))
    rw [ratComplexValue_mul, ← pow_two] at hd
    apply hd.trans
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr (hr ⟨j,hj⟩)
  have he := complexExp_scaled1024_certificate (ratComplexValue u) (ratComplexValue u)
    (fun j ↦ ratComplexValue (w j)) (2/(10:ℝ)^60) (2/(10:ℝ)^60) 0 hre hre hnorm
    (by simp) (by norm_num) hseed hstate hstep
  apply he.trans
  norm_num

end ReciprocalXi

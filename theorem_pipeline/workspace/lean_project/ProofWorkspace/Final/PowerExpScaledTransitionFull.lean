import ProofWorkspace.Final.XiThetaCoefficientFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def powerExpScaledFirst (s : ℂ) (c h lambda : ℝ) : ℂ :=
  (s-(lambda*c:ℝ))*(h:ℂ)/(c:ℂ)

def powerExpScaledA (s : ℂ) (c h lambda : ℝ) (n : ℕ) : ℂ :=
  (s-(lambda*c:ℝ)-(n+1:ℕ))*(h:ℂ)/((c:ℂ)*(n+2:ℕ))

def powerExpScaledB (c h lambda : ℝ) (n : ℕ) : ℂ :=
  (lambda:ℂ)*(h:ℂ)^2/((c:ℂ)*(n+2:ℕ))

theorem scaledPowerExpCoefficient_one_eq (s : ℂ) (c h lambda : ℝ) (hc : 0<c) :
    scaledPowerExpCoefficient s (c:ℂ) lambda h 1=
      powerExpScaledFirst s c h lambda*scaledPowerExpCoefficient s (c:ℂ) lambda h 0 := by
  have hz : (c:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc)
  have he := scaledPowerExpCoefficient_one s (c:ℂ) lambda h hz
  have hc0 : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  apply mul_left_cancel₀ hc0
  rw [he]
  unfold powerExpScaledFirst
  push_cast
  field_simp

theorem scaledPowerExpCoefficient_recurrence_eq (s : ℂ) (c h lambda : ℝ) (n : ℕ)
    (hc : 0<c) :
    scaledPowerExpCoefficient s (c:ℂ) lambda h (n+2)=
      powerExpScaledA s c h lambda n*scaledPowerExpCoefficient s (c:ℂ) lambda h (n+1)-
      powerExpScaledB c h lambda n*scaledPowerExpCoefficient s (c:ℂ) lambda h n := by
  have hz : (c:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc)
  have he := scaledPowerExpCoefficient_recurrence s (c:ℂ) lambda h n hz
  have hc0 : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  have hn0 : ((n+2:ℕ):ℂ)≠0 := by exact_mod_cast (by omega : n+2≠0)
  have hn02 : (n:ℂ)+2≠0 := by exact_mod_cast (by omega : n+2≠0)
  apply mul_left_cancel₀ (mul_ne_zero hc0 hn0)
  rw [he]
  unfold powerExpScaledA powerExpScaledB
  push_cast
  field_simp [hc0,hn02]
  <;> ring

theorem powerExpScaledFirst_sub (s : ℂ) (c h lambda mu : ℝ) (hc : c≠0) :
    powerExpScaledFirst s c h lambda-powerExpScaledFirst s c h mu=
      (-((lambda-mu)*h:ℝ):ℂ) := by
  have hc0 : (c:ℂ)≠0 := by exact_mod_cast hc
  unfold powerExpScaledFirst
  push_cast
  field_simp
  <;> ring

theorem powerExpScaledA_sub (s : ℂ) (c h lambda mu : ℝ) (n : ℕ) (hc : c≠0) :
    powerExpScaledA s c h lambda n-powerExpScaledA s c h mu n=
      (-((lambda-mu)*h/(n+2:ℕ):ℝ):ℂ) := by
  have hc0 : (c:ℂ)≠0 := by exact_mod_cast hc
  have hn0 : ((n+2:ℕ):ℂ)≠0 := by exact_mod_cast (by omega : n+2≠0)
  unfold powerExpScaledA
  push_cast
  field_simp
  <;> ring

theorem powerExpScaledB_sub (c h lambda mu : ℝ) (n : ℕ) :
    powerExpScaledB c h lambda n-powerExpScaledB c h mu n=
      (((lambda-mu)*h^2/(c*(n+2:ℕ)):ℝ):ℂ) := by
  unfold powerExpScaledB
  push_cast
  ring

end ReciprocalXi

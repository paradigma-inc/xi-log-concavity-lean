import ProofWorkspace.Final.XiMomentResidualFull
import ProofWorkspace.Final.SourceMomentCapFull
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
open Set
namespace ReciprocalXi

def originalLowRootUpper (j : Fin 3) : ℝ :=
  (momentRootUpperEndpoints.getD j.val 0 : ℝ)

def originalLowRootLower (j : Fin 3) : ℝ := originalLowRootUpper j-4/(10:ℝ)^29

theorem originalLowRootLower_lt_upper (j : Fin 3) :
    originalLowRootLower j<originalLowRootUpper j := by
  unfold originalLowRootLower
  norm_num

theorem originalLowRootLower_pos (j : Fin 3) : 0<originalLowRootLower j := by
  fin_cases j <;> norm_num [originalLowRootLower,originalLowRootUpper,momentRootUpperEndpoints]

theorem originalLowRootUpper_lt_sixty (j : Fin 3) : originalLowRootUpper j<60 := by
  fin_cases j <;> norm_num [originalLowRootUpper,momentRootUpperEndpoints]

theorem originalLowRootInterval_order {i j : Fin 3} (h : i<j) :
    originalLowRootUpper i<originalLowRootLower j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [originalLowRootLower,originalLowRootUpper,momentRootUpperEndpoints] at *

theorem F_exists_real_zero_of_opposite_signs {L U : ℝ} (hLU : L<U)
    (hs : (F (L:ℂ)).re*(F (U:ℂ)).re<0) :
    ∃ x : ℝ, L<x ∧ x<U ∧ F (x:ℂ)=0 := by
  have hf : Continuous (fun x : ℝ ↦ (F (x:ℂ)).re) :=
    Complex.continuous_re.comp (differentiable_F_complex.continuous.comp
      Complex.continuous_ofReal)
  have he : (0:ℝ) ∈ (fun x : ℝ ↦ (F (x:ℂ)).re) '' Icc L U := by
    rcases mul_neg_iff.mp hs with h | h
    · exact intermediate_value_Icc' hLU.le hf.continuousOn ⟨h.2.le,h.1.le⟩
    · exact intermediate_value_Icc hLU.le hf.continuousOn ⟨h.1.le,h.2.le⟩
  obtain ⟨x,hx,hzero⟩ := he
  dsimp only at hzero
  have hL : x≠L := by
    intro hxL
    subst x
    rw [hzero,zero_mul] at hs
    exact (lt_irrefl 0) hs
  have hU : x≠U := by
    intro hxU
    subst x
    rw [hzero,mul_zero] at hs
    exact (lt_irrefl 0) hs
  refine ⟨x,lt_of_le_of_ne hx.1 hL.symm,lt_of_le_of_ne hx.2 hU,?_⟩
  rw [F_real_eq_ofReal_re,hzero,Complex.ofReal_zero]

def OriginalLowRootIntervalExistence : Prop :=
  ∀ j : Fin 3, ∃ x : ℝ, originalLowRootLower j<x ∧ x<originalLowRootUpper j ∧
    F (x:ℂ)=0

theorem originalLowRootIntervalExistence_of_signs
    (hs : ∀ j : Fin 3, (F (originalLowRootLower j:ℂ)).re*
      (F (originalLowRootUpper j:ℂ)).re<0) : OriginalLowRootIntervalExistence := by
  intro j
  exact F_exists_real_zero_of_opposite_signs (originalLowRootLower_lt_upper j) (hs j)

/-- The three original real intervals, with occurrence-level exhaustion and proved simplicity.
    Nonemptiness is not assumed: the theorem below derives it from actual endpoint signs. -/
structure ThreeLowZeroCertificate where
  value : Fin 3 → ℝ
  occurrence : Fin 3 → FPositiveZeroOccurrence
  root_eq : ∀ j, F_pairRoot (occurrence j)=(value j:ℂ)
  lower : ∀ j, originalLowRootLower j<value j
  upper : ∀ j, value j<originalLowRootUpper j
  other_gap : ∀ z : FPositiveZeroOccurrence,
    (∀ j, z≠occurrence j) → 60<(F_pairRoot z).re
  simple : ∀ j, analyticOrderNatAt F (F_pairRoot (occurrence j))=1

theorem threeLowZeroCertificate_of_interval_existence
    (hex : OriginalLowRootIntervalExistence) : Nonempty ThreeLowZeroCertificate := by
  classical
  choose x hxL hxU hxzero using hex
  have hxpos (j : Fin 3) : 0<x j := (originalLowRootLower_pos j).trans (hxL j)
  let occ (j : Fin 3) : FPositiveZeroOccurrence :=
    ⟨⟨⟨(x j:ℂ),hxzero j⟩,⟨0,F_zero_order_pos _ (hxzero j)⟩⟩,
      by simpa using hxpos j⟩
  have hroot (j : Fin 3) : F_pairRoot (occ j)=(x j:ℂ) := rfl
  have hmono : StrictMono x := by
    intro i j hij
    exact (hxU i).trans ((originalLowRootInterval_order hij).trans (hxL j))
  have hinj : Function.Injective occ := by
    intro i j he
    apply hmono.injective
    apply Complex.ofReal_injective
    exact (hroot i).symm.trans ((congrArg F_pairRoot he).trans (hroot j))
  have hgap (z : FPositiveZeroOccurrence) (hz : ∀ j, z≠occ j) :
      60<(F_pairRoot z).re := by
    exact F_three_real_occurrences_exhaust_below_sixty (occ 0) (occ 1) (occ 2)
      (x 0) (x 1) (x 2) (hroot 0) (hroot 1) (hroot 2)
      (hxpos 0) (hxpos 1) (hxpos 2) (hxU 0).le (hxU 1).le (hxU 2).le
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      z (hz 0) (hz 1) (hz 2)
  have hsimple (j : Fin 3) : analyticOrderNatAt F (F_pairRoot (occ j))=1 := by
    apply F_pairRoot_simple_of_unique_occurrence
    intro z hz
    have hre : (F_pairRoot z).re=x j := by rw [hz,hroot,Complex.ofReal_re]
    have hexocc : ∃ i : Fin 3, z=occ i := by
      by_contra hn
      push_neg at hn
      have h := hgap z hn
      rw [hre] at h
      exact (h.trans ((hxU j).trans (originalLowRootUpper_lt_sixty j))).false
    obtain ⟨i,hi⟩ := hexocc
    have hval : x i=x j := by simpa only [hi,hroot,Complex.ofReal_re] using hre
    exact hi.trans (congrArg occ (hmono.injective hval))
  exact ⟨⟨x,occ,hroot,hxL,hxU,hgap,hsimple⟩⟩

theorem threeLowZeroCertificate_of_signs
    (hs : ∀ j : Fin 3, (F (originalLowRootLower j:ℂ)).re*
      (F (originalLowRootUpper j:ℂ)).re<0) : Nonempty ThreeLowZeroCertificate :=
  threeLowZeroCertificate_of_interval_existence (originalLowRootIntervalExistence_of_signs hs)

theorem ThreeLowZeroCertificate.value_strictMono (C : ThreeLowZeroCertificate) :
    StrictMono C.value := by
  intro i j hij
  exact (C.upper i).trans ((originalLowRootInterval_order hij).trans (C.lower j))

theorem ThreeLowZeroCertificate.occurrence_injective (C : ThreeLowZeroCertificate) :
    Function.Injective C.occurrence := by
  intro i j he
  apply C.value_strictMono.injective
  apply Complex.ofReal_injective
  exact (C.root_eq i).symm.trans ((congrArg F_pairRoot he).trans (C.root_eq j))

theorem ThreeLowZeroCertificate.exhaustion (C : ThreeLowZeroCertificate)
    (z : FPositiveZeroOccurrence) (hz : (F_pairRoot z).re≤60) :
    ∃ j : Fin 3, z=C.occurrence j := by
  by_contra hn
  push_neg at hn
  exact (C.other_gap z hn).not_ge hz

end ReciprocalXi

import FullAuditConditionalExercises
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MeasureTheory Set
namespace Asakura.FullAudit

/-- The sigma algebra whose sets are unions of fibers of q, written so its
measurability condition is available directly in the finite counterexample. -/
def fiberSigma {Ω β : Type*} (q : Ω → β) : MeasurableSpace Ω where
  MeasurableSet' A := ∀ x y, q x = q y → (x ∈ A ↔ y ∈ A)
  measurableSet_empty := by simp
  measurableSet_compl := by
    intro A hA x y hxy
    exact not_congr (hA x y hxy)
  measurableSet_iUnion := by
    intro A hA x y hxy
    simp only [mem_iUnion]
    exact exists_congr fun n => hA n x y hxy

noncomputable def threePointLaw : Measure (Fin 3) := (PMF.uniformOfFintype (Fin 3)).toMeasure
instance : IsProbabilityMeasure threePointLaw := by unfold threePointLaw; infer_instance

def leftGroup (i : Fin 3) : Bool := i == 0
def middleGroup (i : Fin 3) : Bool := i == 1

theorem two_fiber_sigmas_intersection : fiberSigma leftGroup ⊓ fiberSigma middleGroup = ⊥ := by
  apply le_antisymm
  · intro A hA
    change (∀ x y, leftGroup x = leftGroup y → (x ∈ A ↔ y ∈ A)) ∧
      (∀ x y, middleGroup x = middleGroup y → (x ∈ A ↔ y ∈ A)) at hA
    have h01 := hA.2 0 2 (by decide)
    have h12 := hA.1 1 2 (by decide)
    have hc (i : Fin 3) : i ∈ A ↔ 0 ∈ A := by
      fin_cases i
      · rfl
      · exact h12.trans h01.symm
      · exact h01.symm
    by_cases h0 : 0 ∈ A
    · have : A = univ := Set.ext fun i => by simp [(hc i).mpr h0]
      simp [this]
    · have : A = ∅ := Set.ext fun i => by simp [hc i,h0]
      simp [this]
  · exact bot_le

/-- Exact integration on the equal-weight three-point probability space. -/
theorem threePoint_integral (f : Fin 3 → ℝ) :
    ∫ i, f i ∂threePointLaw = (f 0 + f 1 + f 2)/3 := by
  simp [threePointLaw, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fin.sum_univ_succ, smul_eq_mul]
  ring


def threePointX (i : Fin 3) : ℝ := if i = 0 then 1 else 0
noncomputable def threePointZ (i : Fin 3) : ℝ := if i = 1 then 0 else 1/2

theorem threePointX_left_measurable : Measurable[fiberSigma leftGroup] threePointX := by
  intro B hB x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [leftGroup, threePointX]

theorem threePointZ_middle_measurable : Measurable[fiberSigma middleGroup] threePointZ := by
  intro B hB x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [middleGroup, threePointZ]

/-- The cell-average computation is verified by the integral characterization,
not asserted as an unexplained numerical counterexample. -/
theorem threePoint_conditional_formula :
    threePointLaw[threePointX | fiberSigma middleGroup] =ᵐ[threePointLaw] threePointZ := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (show fiberSigma middleGroup ≤ ⊤ from le_top)
    (show Integrable threePointX threePointLaw from .of_finite)
    (fun _ _ _ => (show Integrable threePointZ threePointLaw from .of_finite).integrableOn) _
    threePointZ_middle_measurable.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have h02 : (0 : Fin 3) ∈ A ↔ (2 : Fin 3) ∈ A := hA 0 2 (by decide)
  rw [← integral_indicator (MeasurableSet.of_discrete (s := A)),
    ← integral_indicator (MeasurableSet.of_discrete (s := A)), threePoint_integral, threePoint_integral]
  by_cases h0 : (0 : Fin 3) ∈ A <;> by_cases h1 : (1 : Fin 3) ∈ A <;>
    simp_all [Set.indicator, threePointX, threePointZ] <;> norm_num

/-- Exercise 1.5.2: explicit failure of the unrestricted iterated-conditioning identity. -/
theorem conditional_expectations_do_not_commute :
    ¬ (threePointLaw[threePointLaw[threePointX | fiberSigma leftGroup] | fiberSigma middleGroup]
      =ᵐ[threePointLaw] threePointLaw[threePointX | fiberSigma leftGroup ⊓ fiberSigma middleGroup]) := by
  have hx : threePointLaw[threePointX | fiberSigma leftGroup] = threePointX :=
    condExp_of_stronglyMeasurable (show fiberSigma leftGroup ≤ ⊤ from le_top)
      threePointX_left_measurable.stronglyMeasurable .of_finite
  rw [hx, two_fiber_sigmas_intersection, condExp_bot]
  have hmean : ∫ i, threePointX i ∂threePointLaw = 1/3 := by
    rw [threePoint_integral]
    norm_num [threePointX]
  rw [hmean]
  intro h
  have he := threePoint_conditional_formula.symm.trans h
  have hneq : ∀ i, threePointZ i ≠ (1:ℝ)/3 := by
    intro i; fin_cases i <;> norm_num [threePointZ]
  have hf : ∀ᵐ i ∂threePointLaw, False := he.mono fun i hi => hneq i hi
  exact hf.exists.choose_spec

end Asakura.FullAudit

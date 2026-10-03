import Chapter9ConditionalFubini
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The monotone-class step from finite-observation cylinders to all the
information they generate. The equalities tested here are actual set integrals. -/
theorem conditional_expectation_of_pi_system {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (C : Set (Set Ω)) (hpi : IsPiSystem C) (hgen : G=MeasurableSpace.generateFrom C)
    (hu : univ∈C) (Y Z : Ω → ℝ) (hY : Integrable Y P) (hZ : Integrable Z P)
    (hmZ : AEStronglyMeasurable[G] Z P)
    (he : ∀ A∈C,(∫ w in A,Y w ∂P)=(∫ w in A,Z w ∂P)) :
    P[Y|G]=ᵐ[P] Z := by
  letI : MeasurableSpace Ω := m
  have hme A (hA : A∈C) : MeasurableSet[G] A := hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
  have hv : (P.withDensityᵥ Y).trim hG=(P.withDensityᵥ Z).trim hG := by
    apply VectorMeasure.ext_of_generateFrom C _ hgen hpi _
    · intro A hA
      rw [hY.withDensityᵥ_trim_eq_integral hG (hme A hA),hZ.withDensityᵥ_trim_eq_integral hG (hme A hA)]
      exact he A hA
    · rw [hY.withDensityᵥ_trim_eq_integral hG MeasurableSet.univ,
        hZ.withDensityᵥ_trim_eq_integral hG MeasurableSet.univ]
      exact he univ hu
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hY (fun A _ _ => hZ.integrableOn) ?_ hmZ).symm
  intro A hA _
  have hh := congrArg (fun v => v A) hv
  rw [hY.withDensityᵥ_trim_eq_integral hG hA,hZ.withDensityᵥ_trim_eq_integral hG hA] at hh
  exact hh.symm
end Asakura.Chapter9

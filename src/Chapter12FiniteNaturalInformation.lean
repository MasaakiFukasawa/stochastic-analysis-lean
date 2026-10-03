import Chapter12BrownianCylinderDensity

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon Brownian information is contained in the information of
all nonnegative finite times, including after passing from the terminal space
back to the ambient probability measure. -/
theorem finite_brownian_natural_information {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T : ℝ) (U : Ω → ℝ)
    (hU : AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P B T z w) inferInstance] U
        (P.trim (B.le (realTimeClamp T)))) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w (z : Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}) =>
        B.W z.1 (realTimeClamp z.2.val) w) inferInstance] U P := by
  let K := Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}
  let e : BrownianTimeCoordinates d T → K := fun z => ⟨z.1,z.2.val,z.2.property.1,EReal.coe_lt_top _⟩
  have hr : Measurable (fun f : K → ℝ => fun z : BrownianTimeCoordinates d T => f (e z)) :=
    Measurable.of_eval (fun z => measurable_pi_apply (e z))
  apply (hU.of_trim (B.le _)).mono
  exact MeasurableSpace.comap_le_comap_of_eq_comp _ hr rfl

end Asakura.Chapter12

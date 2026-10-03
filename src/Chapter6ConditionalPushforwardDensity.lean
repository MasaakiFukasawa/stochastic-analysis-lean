import Chapter6LikelihoodPushforward
import FullAuditFactorizationExercise
import Chapter6DensityConditional

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The density of the observed marginal is the conditional expectation
of the actual positive change-of-measure density, expressed as a Borel
function of the observation. -/
theorem conditional_pushforward_density {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P Q : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) (D : Ω → ℝ) (hD : Integrable D P)
    (hp : ∀ᵐ w ∂P,0<D w) (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (D w))) :
    ∃ r : E → ℝ,Measurable r ∧
      P[D|MeasurableSpace.comap X inferInstance]=r ∘ X ∧
      (∀ᵐ y ∂P.map X,0<r y) ∧
      Q.map X=(P.map X).withDensity (fun y => ENNReal.ofReal (r y)) := by
  let G := MeasurableSpace.comap X inferInstance
  have hG : G≤m := hX.comap_le
  obtain ⟨r,hr,he⟩ := measurable_factorization_written X (P[D|G]) stronglyMeasurable_condExp.measurable
  have hpos := exercise_ce_strictly_positive P hG hD hp
  letI : MeasurableSpace Ω := m
  refine ⟨r,hr,he,?_,?_⟩
  · apply (ae_map_iff hX.aemeasurable (hr measurableSet_Ioi)).mpr
    simpa only [he,Function.comp_apply,mem_Ioi] using hpos
  · have hmap : Q.map X=(P.withDensity (fun w => ENNReal.ofReal (r (X w)))).map X := by
      ext A hA
      rw [Measure.map_apply hX hA,Measure.map_apply hX hA,hQ,
        withDensity_apply _ (hX hA),withDensity_apply _ (hX hA)]
      have hCEi : Integrable (fun w => r (X w)) P := by
        change Integrable (r ∘ X) P
        rw [← he]
        exact integrable_condExp
      have hCEp : ∀ᵐ w ∂P,0≤r (X w) := by
        simpa only [he,Function.comp_apply] using hpos.mono (fun _ h => h.le)
      rw [← ofReal_integral_eq_lintegral_ofReal hD.integrableOn (ae_restrict_of_ae (hp.mono (fun _ h => h.le))),
        ← ofReal_integral_eq_lintegral_ofReal hCEi.integrableOn (ae_restrict_of_ae hCEp)]
      congr 1
      have hAG : MeasurableSet[G] (X ⁻¹' A) := ⟨A,hA,rfl⟩
      simpa only [he,Function.comp_apply] using (setIntegral_condExp hG hD hAG).symm
    rw [hmap]
    exact likelihood_pushforward P X hX _ hr.ennreal_ofReal

end Asakura.Chapter6
